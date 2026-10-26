import * as Tone from 'https://esm.sh/tone@14.7.77';
import { Muxer, ArrayBufferTarget } from 'https://esm.sh/mp4-muxer';

﻿﻿// --- Configuration ---
const BASE_VISUAL_SPEED = 1000; // Base px/sec scroll speed
const MAX_VOICES = 64; // Reduced to prevent audio engine dropouts/lag
const VELOCITY_THRESHOLD = 25; // Minimum MIDI velocity to actually play a note
const VISUAL_LOOKAHEAD = 2.0; 
const AUDIO_FRAME_BUDGET_MS = 1.5; 
const MAX_NOTES_PER_FRAME = 32; 
const KEYBOARD_HEIGHT = 80;

class MidiApp {
    constructor() {
        this.canvas = document.createElement('canvas');
        this.ctx = this.canvas.getContext('2d', { alpha: false });
        
        this.midiData = null;
        this.isPlaying = false;
        this.currentTime = 0;
        this.lastUpdateTime = 0;
        
        this.noteCount = 0;

        // Song note range (MIDI note numbers)
        this.songMinNote = null;
        this.songMaxNote = null;

        // Keyboard layout
        this.keyCount = 128;
        this.midiStartNote = 0;
        this.noteChunks = [];
        this.noteChunksU32 = [];
        this.NOTES_PER_CHUNK = 1000000;
        this.trackColors = [];
        this.trackColorStrings = [];
        this.maxNoteDuration = 0;

        // Coloring mode: 'track', 'channel', 'note', 'velocity', 'octave', or 'track-channel'
        this.colorMode = 'track';
        this.trackCount = 0;

        // Tempo / BPM
        this.tempoMap = null;
        this.division = 0;
        this.currentBpm = 0;
        this.visualSpeed = BASE_VISUAL_SPEED;

        // Render mode: "time", "fake-tick", or "real-tick"
        this.renderMode = 'time';
        this.currentTick = 0;
        this.pixelsPerTickBase = 0;

        // Render quality: 'optimized' (merged rects), 'unnecessary' (delayed spawn/early despawn), 'strict' (per-note rects), or 'absurd' (all notes, no culling)
        this.renderQuality = 'optimized';
        
        this.cachedStartIdx = 0;
        this.cachedEndIdx = 0;
        this.lastCacheTime = -1;

        this.audioPointer = 0;
        this.timeIndexTable = null; 
        this.keyExpirations = new Float32Array(this.keyCount);
        // Per-key color hue (0–359), -1 = none
        this.keyColorHues = new Int16Array(this.keyCount).fill(-1);
        // Store the packed note word that last lit each key (-1 = none)
        this.keyPackedNotes = new Int32Array(this.keyCount).fill(-1);
        // Support up to 512 different "keys" for trigger de-duplication
        this.lastPitchTriggerTimes = new Float32Array(512).fill(-1);

        // MIDI output routing
        this.midiAccess = null;
        this.midiOutputs = [];
        this.currentMidiOut = null;
        this.midiOutMode = 'internal';

        // Pre-rendered Audio State
        this.audioMode = 'realtime';
        this.renderedChunks = new Map();
        this.renderingChunks = new Set();
        this.scheduledChunks = new Map();
        this.fullAudioBuffer = null;
        this.fullAudioSource = null;
        this.currentMidiId = 0;
        this.activeRenders = 0;
        this.MAX_CONCURRENT_RENDERS = 2;
        // Larger chunks to reduce scheduling overhead and frequency of swaps
        this.CHUNK_DURATION = 8;
        this.isRendering = false;
        // Mapping between song-time and audio-context time while playing
        this.playbackStartSongTime = 0;
        this.playbackStartAudioTime = 0;

        // Video Export State
        this.isExporting = false;
        this.exportCancelled = false;
        this.mediaRecorder = null;
        this.recordedChunks = [];
        this.currentFileName = "midi_render";

        // Pre-bound helper for mapping MIDI notes to visible key indices
        this.midiToKeyIndex = (midi) => this.getKeyIndexForMidi(midi);
        
        this.lastFpsTime = performance.now();
        this.frames = 0;
        this.fpsElement = document.getElementById('fps-counter');
        this.noteCounterEl = document.getElementById('note-counter');
        this.npsCounterEl = document.getElementById('nps-counter');
        this.bpmCounterEl = document.getElementById('bpm-counter');
        
        this.npsBuckets = new Uint32Array(10);
        this.lastBucketIndex = 0;
        this.lastBucketTime = 0;

        // Initialize Worker
        this.worker = new Worker('midi-worker.js');
        this.worker.onmessage = (e) => this.handleWorkerMessage(e.data);

        this.init();
    }

    async init() {
        this.resize();
        document.getElementById('container').appendChild(this.canvas);
        this.setupAudio();
        this.setupEventListeners();
        await this.initMidiOutputs();
        this.animate();
        document.getElementById('play-btn').textContent = 'Play';
        document.getElementById('play-btn').disabled = false;
    }

    resize() {
        const dpr = window.devicePixelRatio || 1;
        this.canvas.width = window.innerWidth * dpr;
        this.canvas.height = window.innerHeight * dpr;
        this.canvas.style.width = window.innerWidth + 'px';
        this.canvas.style.height = window.innerHeight + 'px';
        this.ctx.resetTransform();
        this.ctx.scale(dpr, dpr);

        const count = this.keyCount || 128;
        this.keyWidth = window.innerWidth / count;
        
        // Pre-calculate visual constants
        this.xOffsets = new Float32Array(count);
        this.drawWidth = this.keyWidth * 0.8;
        const xMargin = this.keyWidth * 0.1;
        for (let i = 0; i < count; i++) {
            this.xOffsets[i] = i * this.keyWidth + xMargin;
        }
    }

    setupAudio() {
        // Precompute frequencies for up to 512 keys (visual range)
        this.freqTable = new Float32Array(512);
        for (let i = 0; i < 512; i++) {
            this.freqTable[i] = 440 * Math.pow(2, (i - 69) / 12);
        }

        // Use a simpler oscillator and optimized synth settings for high NPS
        // Main limiter for all audio output
        this.limiter = new Tone.Limiter(-1).toDestination();
        
        // Create a Tone.Gain bridge to properly register with Tone's graph
        this.prerenderedEntry = new Tone.Gain().connect(this.limiter);

        this.synth = new Tone.PolySynth(Tone.Synth, {
            oscillator: { type: 'pulse', width: 0.5 },
            envelope: { attack: 0.005, decay: 0.1, sustain: 0.1, release: 0.05 }
        }).connect(this.limiter);
        this.synth.maxPolyphony = MAX_VOICES;
    }

    async initMidiOutputs() {
        const select = document.getElementById('midi-out-select');
        if (!navigator.requestMIDIAccess || !select) return;

        try {
            this.midiAccess = await navigator.requestMIDIAccess();
            this.refreshMidiOutputs();
            this.midiAccess.onstatechange = () => this.refreshMidiOutputs();
        } catch (e) {
            // If MIDI is not available or user blocks access, keep internal synth only
        }
    }

    refreshMidiOutputs() {
        const select = document.getElementById('midi-out-select');
        if (!select) return;

        const previousValue = select.value;

        // Clear all options
        while (select.firstChild) select.removeChild(select.firstChild);

        // Always add internal synth option first
        const internalOption = document.createElement('option');
        internalOption.value = 'internal';
        internalOption.textContent = 'Internal Synth';
        select.appendChild(internalOption);

        this.midiOutputs = [];

        if (this.midiAccess) {
            for (const output of this.midiAccess.outputs.values()) {
                this.midiOutputs.push(output);
                const opt = document.createElement('option');
                opt.value = output.id;
                opt.textContent = output.name || `MIDI Out ${this.midiOutputs.length}`;
                select.appendChild(opt);
            }
        }

        // Restore selection when possible
        if ([...select.options].some(o => o.value === previousValue)) {
            select.value = previousValue;
        } else {
            select.value = 'internal';
        }

        // Update routing state
        if (select.value === 'internal') {
            this.currentMidiOut = null;
            this.midiOutMode = 'internal';
        } else {
            this.currentMidiOut = this.midiOutputs.find(o => o.id === select.value) || null;
            this.midiOutMode = this.currentMidiOut ? 'external' : 'internal';
        }
    }

    async loadMidi(file) {
        document.getElementById('loading-overlay').style.display = 'flex';
        document.getElementById('load-progress').style.width = '0%';
        document.getElementById('loading-text').textContent = "Initializing Parser...";
        document.getElementById('loading-subtext').textContent = "Slicing file...";
        document.getElementById('filename').textContent = file.name;

        try {
            this.currentFileName = file.name.replace(/\.[^/.]+$/, "");
            // Post the file object directly. Workers can handle Blobs/Files without copying.
            this.worker.postMessage({ file });
        } catch (err) {
            alert("Failed to start worker: " + err.message);
            document.getElementById('loading-overlay').style.display = 'none';
        }
    }

    handleWorkerMessage(data) {
        if (data.type === 'init-filename') {
            this.currentFileName = data.name || "midi_render";
            return;
        }

        if (data.type === 'rendered-chunk') {
            if (data.myMidiId !== this.currentMidiId) return;
            
            const ac = Tone.getContext().rawContext;
            const buffer = ac.createBuffer(1, data.audioData.length, ac.sampleRate);
            buffer.getChannelData(0).set(data.audioData);
            
            this.renderedChunks.set(data.chunkIdx, { 
                buffer, 
                chunkStartTime: data.chunkIdx * this.CHUNK_DURATION, 
                duration: this.CHUNK_DURATION 
            });
            this.renderingChunks.delete(data.chunkIdx);
            this.activeRenders--;
            return;
        }

        if (data.type === 'full-audio-done') {
            if (data.myMidiId !== this.currentMidiId) return;
            
            // Restore note data ownership
            this.noteChunks = data.noteChunks;
            this.noteChunksU32 = this.noteChunks.map(c => new Uint32Array(c.buffer, c.byteOffset, c.length));

            const ac = Tone.getContext().rawContext;
            const buffer = ac.createBuffer(1, data.audioData.length, ac.sampleRate);
            buffer.getChannelData(0).set(data.audioData);
            this.fullAudioBuffer = buffer;
            
            document.getElementById('loading-overlay').style.display = 'none';
            document.getElementById('status').textContent = 'Ready (Rendered)';
            document.getElementById('play-btn').disabled = false;
            document.getElementById('play-btn').textContent = 'Play';
            document.getElementById('video-export-open-btn').disabled = false;
            return;
        }

        const progressEl = document.getElementById('load-progress');
        const loadingText = document.getElementById('loading-text');
        const subText = document.getElementById('loading-subtext');

        if (data.type === 'progress') {
            progressEl.style.width = data.progress + '%';
            loadingText.textContent = data.text;
            if (data.subtext) subText.textContent = data.subtext;
        } else if (data.type === 'done') {
            this.currentMidiId++;
            this.stopCurrentAudio();
            this.renderedChunks.clear();
            this.renderingChunks.clear();
            this.scheduledChunks.clear();
            this.fullAudioBuffer = null;
            this.activeRenders = 0;
            
            this.noteChunks = data.noteChunks;
            this.noteChunksU32 = this.noteChunks.map(c => new Uint32Array(c.buffer, c.byteOffset, c.length));
            this.NOTES_PER_CHUNK = data.notesPerChunk;
            this.noteCount = data.noteCount;
            this.trackCount = data.trackCount || 0;
            this.maxNoteDuration = data.maxNoteDuration || 5.0;
            this.midiData = { duration: data.duration };

            // Song note range from worker (clamped to 0–127 there)
            this.songMinNote = (typeof data.minNote === 'number') ? data.minNote : null;
            this.songMaxNote = (typeof data.maxNote === 'number') ? data.maxNote : null;

            // Store tempo information for BPM detection
            this.tempoMap = data.tempoMap || null;
            this.division = data.division || 0;

            // Precompute a base pixels-per-tick for real tick-based rendering.
            // Baseline: at 120 BPM, scroll speed ≈ BASE_VISUAL_SPEED.
            if (this.division > 0) {
                const ticksPerSecondAt120 = (120 / 60) * this.division; // beats/sec * ticks/beat
                this.pixelsPerTickBase = BASE_VISUAL_SPEED / ticksPerSecondAt120;
            } else {
                this.pixelsPerTickBase = 0;
            }
            
            // Pre-allocate buckets and colors (0–359 hue slots)
            this.buckets = Array.from({ length: 360 }, () => []);
            // Use a small set of bright, high-contrast hues and quantize indices onto them
            const DISTINCT_STEPS = 24;
            const stepSize = 360 / DISTINCT_STEPS;
            this.trackColorStrings = new Array(360);
            for (let i = 0; i < 360; i++) {
                const stepIndex = Math.round((i / 359) * (DISTINCT_STEPS - 1));
                const hue = Math.round(stepIndex * stepSize) % 360;
                const lightness = (stepIndex % 2 === 0) ? 50 : 70; // alternate light/dark for contrast
                this.trackColorStrings[i] = `hsl(${hue}, 100%, ${lightness}%)`;
            }
            this.trackColors = this.trackColorStrings;
            
            this.buildIndexTable();
            
            if (this.audioMode === 'full-rendered') {
                this.requestFullRender();
            } else {
                document.getElementById('loading-overlay').style.display = 'none';
                document.getElementById('status').textContent = 'Ready';
                document.getElementById('video-export-open-btn').disabled = false;
            }

            // Align keyboard window to the selected layout (fixed 0-based range)
            this.applySongRangeToKeyboard();
        } else if (data.type === 'error') {
            alert("Worker Error: " + data.error);
            document.getElementById('loading-overlay').style.display = 'none';
        }
    }

    getNoteTime(idx) {
        if (!this.noteChunks || this.noteChunks.length === 0) return 0;
        const c = (idx / this.NOTES_PER_CHUNK) | 0;
        if (c >= this.noteChunks.length) return 0;
        const i = (idx % this.NOTES_PER_CHUNK) * 3;
        const chunk = this.noteChunks[c];
        return chunk ? chunk[i] : 0;
    }

    buildIndexTable() {
        if (this.noteCount === 0) return;
        const lastNoteTime = this.getNoteTime(this.noteCount - 1);
        const tableDensity = 10;
        const tableSize = Math.ceil((lastNoteTime + 5) * tableDensity);
        this.timeIndexTable = new Uint32Array(tableSize);
        let cur = 0;
        for (let i = 0; i < tableSize; i++) {
            const t = i / tableDensity;
            while (cur < this.noteCount && this.getNoteTime(cur) < t) cur++;
            this.timeIndexTable[i] = cur;
        }
    }

    setupEventListeners() {
        const playBtn = document.getElementById('play-btn');
        const fileInput = document.getElementById('file-input');
        const uploadBtn = document.getElementById('upload-btn');
        const dropZone = document.getElementById('drop-zone');
        const renderModeSelect = document.getElementById('render-mode-select');
        const keyLayoutSelect = document.getElementById('key-layout-select');
        const midiOutSelect = document.getElementById('midi-out-select');
        const colorModeSelect = document.getElementById('color-mode-select');
        const renderQualitySelect = document.getElementById('render-quality-select');
        const audioModeSelect = document.getElementById('audio-mode-select');
        const videoExportOpenBtn = document.getElementById('video-export-open-btn');
        const exportStartBtn = document.getElementById('export-start-btn');
        const modalCancelBtn = document.getElementById('modal-cancel-btn');
        const exportCancelBtn = document.getElementById('export-cancel-btn');
        const exportModal = document.getElementById('export-modal');

        videoExportOpenBtn.onclick = () => {
            exportModal.style.display = 'flex';
        };

        modalCancelBtn.onclick = () => {
            exportModal.style.display = 'none';
        };

        playBtn.onclick = async () => {
            if (Tone.context.state !== 'running') await Tone.start();
            if (this.isPlaying) this.pausePlayback(); else this.startPlayback();
        };

        uploadBtn.onclick = () => fileInput.click();
        fileInput.onchange = (e) => { if (e.target.files[0]) this.loadMidi(e.target.files[0]); };

        renderModeSelect.onchange = (e) => {
            const v = e.target.value;
            if (v === 'fake-tick' || v === 'real-tick' || v === 'time') {
                this.renderMode = v;
            } else {
                this.renderMode = 'time';
            }

            // When entering a tick-based mode, sync the tick cursor with the current time
            if (this.renderMode !== 'time' && this.tempoMap && this.tempoMap.length > 0) {
                this.currentTick = this.timeToTick(this.currentTime);
            }
        };

        if (midiOutSelect) {
            midiOutSelect.onchange = (e) => {
                const value = e.target.value;
                if (value === 'internal') {
                    this.currentMidiOut = null;
                    this.midiOutMode = 'internal';
                } else {
                    this.currentMidiOut = this.midiOutputs
                        ? this.midiOutputs.find(o => o.id === value) || null
                        : null;
                    this.midiOutMode = this.currentMidiOut ? 'external' : 'internal';
                }
            };
        }

        if (keyLayoutSelect) {
            keyLayoutSelect.onchange = (e) => {
                this.setKeyboardLayout(e.target.value);
            };
        }

        if (colorModeSelect) {
            colorModeSelect.onchange = (e) => {
                const value = e.target.value;
                if (
                    value === 'track' ||
                    value === 'channel' ||
                    value === 'note' ||
                    value === 'velocity' ||
                    value === 'octave' ||
                    value === 'track-channel'
                ) {
                    this.colorMode = value;
                } else {
                    this.colorMode = 'track';
                }
            };
        }

        if (renderQualitySelect) {
            renderQualitySelect.onchange = (e) => {
                const value = e.target.value;
                if (
                    value === 'optimized' ||
                    value === 'unnecessary' ||
                    value === 'strict' ||
                    value === 'absurd'
                ) {
                    this.renderQuality = value;
                } else {
                    this.renderQuality = 'optimized';
                }
            };
        }

        if (audioModeSelect) {
            audioModeSelect.onchange = (e) => {
                this.audioMode = e.target.value;
                if (this.audioMode === 'full-rendered' && !this.fullAudioBuffer && this.midiData) {
                    this.requestFullRender();
                }
                if (this.isPlaying) {
                    this.stopCurrentAudio();
                    this.startCurrentAudio();
                }
            };
        }

        if (exportStartBtn) {
            exportStartBtn.onclick = () => {
                exportModal.style.display = 'none';
                this.startVideoExport();
            };
        }

        if (exportCancelBtn) {
            exportCancelBtn.onclick = () => this.stopVideoExport(true);
        }

        window.addEventListener('dragover', (e) => { e.preventDefault(); dropZone.style.display = 'flex'; });
        dropZone.addEventListener('dragleave', (e) => { e.preventDefault(); dropZone.style.display = 'none'; });
        window.addEventListener('drop', (e) => {
            e.preventDefault();
            dropZone.style.display = 'none';
            if (e.dataTransfer.files[0]) this.loadMidi(e.dataTransfer.files[0]);
        });
        window.addEventListener('resize', () => this.resize());
    }

    setKeyboardLayout(layout) {
        let newKeyCount = 128;

        switch (layout) {
            case '88':
                newKeyCount = 88;
                break;
            case '128':
                newKeyCount = 128;
                break;
            case '256':
                newKeyCount = 256;
                break;
            case '512':
                newKeyCount = 512;
                break;
            default:
                newKeyCount = 128;
                break;
        }

        this.keyCount = newKeyCount;

        // Recompute which keys are visible for this key range
        this.applySongRangeToKeyboard();
    }

    // Adjust the visible key window [midiStartNote, midiStartNote + keyCount)
    // to always cover keys 0..keyCount-1 for the selected layout.
    applySongRangeToKeyboard() {
        if (!this.keyCount || this.keyCount <= 0) return;

        // For 88-key, use standard piano range A0 (21) to C8 (108).
        // For 128/256/512 layouts, use a fixed 0-based range (0..keyCount-1).
        if (this.keyCount === 88) {
            this.midiStartNote = 21;
        } else {
            this.midiStartNote = 0;
        }

        // Recreate per-key buffers for the new layout / range
        this.keyExpirations = new Float32Array(this.keyCount);
        this.keyColorHues = new Int16Array(this.keyCount).fill(-1);
        this.lastYTopF = null;
        this.lastYBottomF = null;

        this.resize();
        this.resetPlayback();
    }

    /**
     * Map a note number to a visible key index [0, keyCount)
     * using a simple contiguous window starting at midiStartNote.
     */
    getKeyIndexForMidi(midi) {
        if (this.keyCount <= 0) return null;
        const k = midi - this.midiStartNote;
        return (k < 0 || k >= this.keyCount) ? null : k;
    }

    startPlayback() {
        if (!this.midiData) return;
        this.isPlaying = true;
        this.lastUpdateTime = performance.now();
        document.getElementById('play-btn').textContent = 'Pause';
        document.getElementById('play-btn').classList.add('playing');
        this.audioPointer = this.findNearestIndex(this.currentTime);
        this.startCurrentAudio();
    }

    startCurrentAudio() {
        const ac = Tone.getContext().rawContext;
        if (!ac) return;

        if ((this.audioMode === 'prerendered' || this.audioMode === 'full-rendered')) {
            this.playbackStartSongTime = this.currentTime;
            this.playbackStartAudioTime = ac.currentTime;

            if (this.audioMode === 'full-rendered' && this.fullAudioBuffer) {
                this.fullAudioSource = ac.createBufferSource();
                this.fullAudioSource.buffer = this.fullAudioBuffer;
                // Use Tone.connect to properly route native node into Tone's graph
                Tone.connect(this.fullAudioSource, this.prerenderedEntry);
                
                const offset = Math.max(0, this.currentTime);
                if (offset < this.fullAudioBuffer.duration) {
                    this.fullAudioSource.start(ac.currentTime, offset);
                }
            }
        }
    }

    stopCurrentAudio() {
        for (const source of this.scheduledChunks.values()) {
            try {
                source.stop();
            } catch (e) {}
            try {
                source.disconnect();
            } catch (e) {}
        }
        this.scheduledChunks.clear();

        if (this.fullAudioSource) {
            try {
                this.fullAudioSource.stop();
                this.fullAudioSource.disconnect();
            } catch (e) {}
            this.fullAudioSource = null;
        }

        this.synth.releaseAll();
    }

    pausePlayback() {
        this.isPlaying = false;
        this.stopCurrentAudio();
        document.getElementById('play-btn').textContent = 'Play';
        document.getElementById('play-btn').classList.remove('playing');
        this.playbackStartSongTime = 0;
        this.playbackStartAudioTime = 0;
    }

    resetPlayback() {
        this.pausePlayback();
        this.currentTime = 0;
        this.currentTick = 0;
        this.audioPointer = 0;
        this.stopCurrentAudio();
        this.renderedChunks.clear();
        this.renderingChunks.clear();
        this.playbackStartSongTime = 0;
        this.playbackStartAudioTime = 0;
        if (this.keyExpirations.length !== this.keyCount) {
            this.keyExpirations = new Float32Array(this.keyCount);
        } else {
            this.keyExpirations.fill(0);
        }
        if (!this.keyColorHues || this.keyColorHues.length !== this.keyCount) {
            this.keyColorHues = new Int16Array(this.keyCount).fill(-1);
        } else {
            this.keyColorHues.fill(-1);
        }
        this.lastPitchTriggerTimes.fill(-1);
        document.getElementById('progress-bar').style.width = '0%';
    }

    findNearestIndex(targetTime) {
        if (this.noteCount === 0 || targetTime <= 0 || this.noteChunks.length === 0) return 0;
        if (!this.timeIndexTable) return 0;
        const tableIdx = Math.max(0, Math.floor(targetTime * 10));
        if (tableIdx >= this.timeIndexTable.length) return this.noteCount;
        let low = this.timeIndexTable[tableIdx];
        let high = (tableIdx + 1 < this.timeIndexTable.length) ? this.timeIndexTable[tableIdx + 1] : this.noteCount - 1;
        while (low <= high) {
            const mid = (low + high) >>> 1;
            if (this.getNoteTime(mid) < targetTime) low = mid + 1;
            else high = mid - 1;
        }
        return low;
    }

    // Compute a hue (0–359) for a packed note word based on current color mode
    getHueForPacked(packed) {
        const note = packed & 0x1FF;             // 0–511, we mostly use 0–127
        const velocity = (packed >> 9) & 0x7F;   // 0–127
        const channel = (packed >> 16) & 0x0F;   // 0–15
        const track = (packed >> 20);           // track index

        let colorId = 0;
        let maxId = 1;

        switch (this.colorMode) {
            case 'channel':
                // Pure channel-based coloring (up to 16 distinct hues)
                colorId = channel;
                maxId = 15; // 0–15
                break;

            case 'note':
                // Full rainbow across MIDI note numbers (support up to 512 keys)
                colorId = Math.max(0, Math.min(511, note));
                maxId = 511;
                break;

            case 'velocity':
                // Map low velocity -> red, high velocity -> violet
                colorId = velocity;
                maxId = 127;
                break;

            case 'octave': {
                // Group by octave (0–42 for 0–511)
                const octave = Math.floor(Math.max(0, Math.min(511, note)) / 12);
                colorId = octave;
                maxId = 42;
                break;
            }

            case 'track-channel':
                // Combine track and channel so multi-track, multi-channel files get a lot of variation
                colorId = (track << 4) | channel;
                maxId = Math.max(1, ((this.trackCount || 1) << 4) - 1);
                break;

            case 'track':
            default:
                // Track mode: if there's only a single track, fall back to a full note rainbow
                if (this.trackCount && this.trackCount > 1) {
                    colorId = track;
                    maxId = Math.max(1, this.trackCount - 1);
                } else {
                    colorId = Math.max(0, Math.min(127, note));
                    maxId = 127;
                }
                break;
        }

        if (maxId <= 0) return 0;
        const hue = (colorId / maxId) * 359;
        return Math.max(0, Math.min(359, hue));
    }

    async requestFullRender() {
        if (!this.midiData) return;
        document.getElementById('loading-overlay').style.display = 'flex';
        document.getElementById('loading-text').textContent = "Rendering Full Audio...";
        document.getElementById('loading-subtext').textContent = "Preparing high-quality buffer...";
        document.getElementById('play-btn').disabled = true;
        document.getElementById('play-btn').textContent = "Rendering...";
        
        const ac = Tone.getContext().rawContext;
        const transferList = this.noteChunks.map(c => c.buffer);

        this.worker.postMessage({
            type: 'render-full',
            sampleRate: ac.sampleRate || 44100,
            myMidiId: this.currentMidiId,
            noteChunks: this.noteChunks,
            notesPerChunk: this.NOTES_PER_CHUNK,
            noteCount: this.noteCount
        }, transferList);

        // Detach local references while worker holds them
        this.noteChunks = [];
        this.noteChunksU32 = [];
    }

    async startVideoExport() {
        if (!this.midiData) return alert("Please load a MIDI file first.");
        if (Tone.context.state !== 'running') await Tone.start();

        // 1. Ensure full rendered audio is available
        if (!this.fullAudioBuffer) {
            this.audioMode = 'full-rendered';
            document.getElementById('audio-mode-select').value = 'full-rendered';
            await this.requestFullRender();
            // The requestFullRender will call back when done. 
            // We need to wait for it.
            const checkBuffer = setInterval(() => {
                if (this.fullAudioBuffer) {
                    clearInterval(checkBuffer);
                    this.performVideoExport();
                }
            }, 500);
            return;
        }

        this.performVideoExport();
    }

    async performVideoExport() {
        const resString = document.getElementById('export-res').value;
        const [targetW, targetH] = resString.split('x').map(Number);
        const targetFps = parseInt(document.getElementById('export-fps').value);
        const includeAudio = document.getElementById('export-audio').checked;

        if (!window.VideoEncoder) {
            alert("Your browser does not support high-quality offline video encoding (WebCodecs). Please use Chrome, Edge, or a modern browser.");
            return;
        }

        this.resetPlayback();
        this.isExporting = true;
        this.exportCancelled = false;
        
        this.canvas.width = targetW;
        this.canvas.height = targetH;
        this.canvas.style.width = '100vw'; 
        this.canvas.style.height = '100vh';
        this.ctx.resetTransform();
        this.ctx.scale(1, 1);

        this.keyWidth = targetW / this.keyCount;
        this.xOffsets = new Float32Array(this.keyCount);
        this.drawWidth = this.keyWidth * 0.8;
        const xMargin = this.keyWidth * 0.1;
        for (let i = 0; i < this.keyCount; i++) {
            this.xOffsets[i] = i * this.keyWidth + xMargin;
        }

        this.keyExpirations = new Float32Array(this.keyCount);
        this.keyColorHues = new Int16Array(this.keyCount).fill(-1);

        const ac = Tone.getContext().rawContext;

        // Codec Probing: We prioritize H.264 (avc1) for maximum compatibility.
        // Format: avc1.PPCCLL where PP=Profile, CC=Constraints, LL=Level (in hex).
        const possibleCodecs = [
            'avc1.4d002a', // Main Profile (4d), Level 4.2 (2a)
            'avc1.42e01e', // Constrained Baseline (42e0), Level 3.0 (1e)
            'avc1.4d001e', // Main Profile (4d), Level 3.0 (1e)
            'avc1.64002a', // High Profile (64), Level 4.2 (2a)
            'vp09.00.10.08', // VP9 Profile 0, Level 1.0, 8-bit
            'av01.0.05M.08', // AV1
        ];
        
        let videoCodec = '';
        let muxer = null;
        // Encoder expects RFC 6381, Muxer expects simplified names
        const encoderAudioCodec = 'mp4a.40.2'; 

        for (const codec of possibleCodecs) {
            try {
                // 1. Browser hardware support check
                const support = await VideoEncoder.isConfigSupported({
                    codec,
                    width: targetW,
                    height: targetH,
                    bitrate: 15_000_000,
                    framerate: targetFps
                });
                
                if (!support.supported) continue;

                // 2. Muxer configuration
                // Note: mp4-muxer constructor's 'codec' property expects simplified aliases 
                // like 'avc', 'hevc', 'vp9', 'av1' for the container logic.
                const muxerVideoCodec = codec.startsWith('avc1') ? 'avc' : 
                                        codec.startsWith('vp09') ? 'vp9' : 
                                        codec.startsWith('av01') ? 'av1' : 'avc';

                const testMuxer = new Muxer({
                    target: new ArrayBufferTarget(),
                    video: {
                        codec: muxerVideoCodec,
                        width: targetW,
                        height: targetH
                    },
                    audio: (includeAudio && this.fullAudioBuffer) ? {
                        codec: 'aac',
                        sampleRate: ac.sampleRate,
                        numberOfChannels: 1
                    } : undefined,
                    fastStart: 'in-memory'
                });

                videoCodec = codec;
                muxer = testMuxer;
                break;
            } catch (e) {
                console.warn(`Codec probe failed for ${codec}:`, e);
                continue;
            }
        }

        if (!videoCodec || !muxer) {
            alert("Could not find a supported video codec for this resolution. Try lowering the resolution or using a different browser.");
            this.stopVideoExport(true);
            return;
        }

        const videoEncoder = new VideoEncoder({
            output: (chunk, meta) => muxer.addVideoChunk(chunk, meta),
            error: (e) => console.error("VideoEncoder Error:", e)
        });

        videoEncoder.configure({
            codec: videoCodec,
            width: targetW,
            height: targetH,
            bitrate: 15_000_000, // 15Mbps is plenty for 1080p-4K MIDI renders
            framerate: targetFps
        });

        let audioEncoder = null;
        if (includeAudio && this.fullAudioBuffer) {
            audioEncoder = new AudioEncoder({
                output: (chunk, meta) => muxer.addAudioChunk(chunk, meta),
                error: (e) => console.error("AudioEncoder Error:", e)
            });
            audioEncoder.configure({
                codec: encoderAudioCodec,
                sampleRate: ac.sampleRate,
                numberOfChannels: 1,
                bitrate: 192000
            });
        }

        document.getElementById('export-status-overlay').style.display = 'flex';
        document.getElementById('export-progress-bar').style.width = '0%';
        document.getElementById('export-progress-text').textContent = '0%';

        const totalDuration = this.midiData.duration;
        const timeStep = 1 / targetFps;
        this.currentTime = 0;
        let frameIdx = 0;

        // Audio Export: Fixed-size buffer accumulation to satisfy high-quality encoders
        let audioSamplesRemaining = 0;
        let audioSampleOffset = 0;
        const AUDIO_FRAME_SIZE = 1024; // Standard AAC frame size
        const sampleRate = ac.sampleRate;

        // Fully deterministic offline rendering loop
        while (this.currentTime < totalDuration && !this.exportCancelled) {
            const timestamp = Math.round(this.currentTime * 1_000_000); // Microseconds for WebCodecs

            // Advance simulation state
            this.currentTick = this.timeToTick(this.currentTime);
            const NPC = this.NOTES_PER_CHUNK;
            while (this.audioPointer < this.noteCount && this.getNoteTime(this.audioPointer) < this.currentTime) {
                const cIdx = (this.audioPointer / NPC) | 0;
                const iIdx = (this.audioPointer % NPC) * 3;
                const noteStart = this.noteChunks[cIdx][iIdx];
                const dur = this.noteChunks[cIdx][iIdx + 1];
                const packed = this.noteChunksU32[cIdx][iIdx + 2];
                const midi = packed & 0x1FF;
                const keyIdx = this.getKeyIndexForMidi(midi);
                if (keyIdx !== null) {
                    this.keyExpirations[keyIdx] = noteStart + dur;
                    this.keyColorHues[keyIdx] = Math.floor(this.getHueForPacked(packed));
                }
                this.audioPointer++;
            }

            const bpm = this.getCurrentBpm(this.currentTime);
            this.currentBpm = bpm;
            this.visualSpeed = (this.renderMode === 'fake-tick' && bpm > 0) ? BASE_VISUAL_SPEED * (bpm / 120) : BASE_VISUAL_SPEED;

            // Render current frame
            this.draw();

            // Encode Video
            const frame = new VideoFrame(this.canvas, { timestamp });
            videoEncoder.encode(frame, { keyFrame: frameIdx % 60 === 0 });
            frame.close();

            // Prevent RAM explosion by waiting for the encoder to process backlogged frames.
            if (videoEncoder.encodeQueueSize > 12) {
                await new Promise(r => setTimeout(r, 20));
            }

            // Encode Audio in discrete packets to satisfy AAC requirements
            if (audioEncoder && this.fullAudioBuffer) {
                const totalSamples = this.fullAudioBuffer.length;
                const targetSampleCount = Math.floor((this.currentTime + timeStep) * sampleRate) - audioSampleOffset;
                
                // Push available samples into encoder in AUDIO_FRAME_SIZE chunks
                while (targetSampleCount >= AUDIO_FRAME_SIZE && audioSampleOffset + AUDIO_FRAME_SIZE <= totalSamples) {
                    const chunk = new Float32Array(AUDIO_FRAME_SIZE);
                    chunk.set(this.fullAudioBuffer.getChannelData(0).subarray(audioSampleOffset, audioSampleOffset + AUDIO_FRAME_SIZE));
                    
                    const audioData = new AudioData({
                        format: 'f32',
                        sampleRate: sampleRate,
                        numberOfFrames: AUDIO_FRAME_SIZE,
                        numberOfChannels: 1,
                        timestamp: Math.round((audioSampleOffset / sampleRate) * 1_000_000),
                        data: chunk
                    });
                    
                    audioEncoder.encode(audioData);
                    audioData.close();
                    audioSampleOffset += AUDIO_FRAME_SIZE;
                }
            }

            frameIdx++;
            this.currentTime += timeStep;

            // Update UI every 10 frames to keep the interface responsive during render
            if (frameIdx % 10 === 0) {
                const progress = (this.currentTime / totalDuration) * 100;
                document.getElementById('export-progress-bar').style.width = `${progress}%`;
                document.getElementById('export-progress-text').textContent = `${Math.floor(progress)}%`;
                // Brief yield to allow the browser to handle UI events and garbage collection
                await new Promise(r => setTimeout(r, 1));
            }
        }

        if (!this.exportCancelled) {
            await videoEncoder.flush();
            if (audioEncoder) await audioEncoder.flush();
            muxer.finalize();

            const { buffer } = muxer.target;
            const blob = new Blob([buffer], { type: 'video/mp4' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = `${this.currentFileName}.mp4`;
            a.click();
            URL.revokeObjectURL(url);
        }

        this.stopVideoExport(this.exportCancelled);
    }

    stopVideoExport(cancelled = false) {
        this.exportCancelled = cancelled;
        this.isPlaying = false;
        this.stopCurrentAudio();
        this.isExporting = false;
        this.resize();
        document.getElementById('export-status-overlay').style.display = 'none';
    }

    async renderChunk(chunkIdx) {
        if (!this.midiData || this.renderingChunks.has(chunkIdx)) return;
        if (this.activeRenders >= this.MAX_CONCURRENT_RENDERS) return;

        this.activeRenders++;
        this.renderingChunks.add(chunkIdx);
        
        const ac = Tone.getContext().rawContext;

        const searchStart = Math.max(0, chunkIdx * this.CHUNK_DURATION - 10);
        const searchEnd = (chunkIdx + 1) * this.CHUNK_DURATION + 1;
        const startIdx = this.findNearestIndex(searchStart);
        const endIdx = this.findNearestIndex(searchEnd);
        
        const count = endIdx - startIdx;
        const noteData = new Float32Array(count * 3);
        const noteDataU32 = new Uint32Array(noteData.buffer);
        const NPC = this.NOTES_PER_CHUNK;

        for (let i = 0; i < count; i++) {
            const gIdx = startIdx + i;
            const c = (gIdx / NPC) | 0;
            const idx = (gIdx % NPC) * 3;
            noteData[i * 3] = this.noteChunks[c][idx];
            noteData[i * 3 + 1] = this.noteChunks[c][idx + 1];
            noteDataU32[i * 3 + 2] = this.noteChunksU32[c][idx + 2];
        }

        this.worker.postMessage({
            type: 'render-chunk',
            chunkIdx,
            chunkDuration: this.CHUNK_DURATION,
            sampleRate: ac.sampleRate,
            myMidiId: this.currentMidiId,
            noteData
        }, [noteData.buffer]);
    }

    updateAudio(now) {
        if (this.noteChunks.length === 0) return;
        const startTimeProcessing = performance.now();
        const lookahead = 0.1; 
        const limit = this.currentTime + lookahead; 
        let triggered = 0;
        const NPC = this.NOTES_PER_CHUNK;

        while (this.audioPointer < this.noteCount) {
            if (performance.now() - startTimeProcessing > AUDIO_FRAME_BUDGET_MS) break;
            
            const cIdx = (this.audioPointer / NPC) | 0;
            if (cIdx >= this.noteChunks.length) break;
            const iIdx = (this.audioPointer % NPC) * 3;
            const chunk = this.noteChunks[cIdx];
            const noteStart = chunk[iIdx];
            
            if (noteStart > limit) break;
            
            // Avoid notes too far in the past or already handled
            if (noteStart >= this.currentTime - 0.01) {
                const packed = this.noteChunksU32[cIdx][iIdx + 2];
                const midi = packed & 0x1FF;
                const velocity = (packed >> 9) & 0x7F;
                const track = packed >> 16;

                // Skip notes that are too soft
                if (velocity >= VELOCITY_THRESHOLD) {
                    // Aggressive voice limiting and re-trigger protection
                    if (triggered < MAX_NOTES_PER_FRAME && 
                        this.synth.activeVoices < MAX_VOICES && 
                        midi < this.lastPitchTriggerTimes.length &&
                        (noteStart - this.lastPitchTriggerTimes[midi] > 0.02)) {
                        
                        const dur = chunk[iIdx + 1];
                        this.npsBuckets[this.lastBucketIndex]++;
                        const startTime = now + Math.max(0, noteStart - this.currentTime);

                        if (this.audioMode === 'realtime') {
                            if (this.midiOutMode === 'external' && this.currentMidiOut) {
                                // Send to external MIDI output (channel 1)
                                const noteNumber = midi & 0x7f;
                                const nowMs = performance.now();
                                const sendAt = nowMs + Math.max(0, (startTime - now) * 1000);
                                const noteOn = [0x90, noteNumber, velocity & 0x7f];
                                const noteOff = [0x80, noteNumber, 0];

                                this.currentMidiOut.send(noteOn, sendAt);
                                this.currentMidiOut.send(noteOff, sendAt + Math.max(10, dur * 1000));
                            } else {
                                // Trigger internal synth scaled by MIDI velocity
                                if (midi >= 0 && midi < this.freqTable.length) {
                                    const velNorm = Math.max(0, Math.min(1, velocity / 127));
                                    this.synth.triggerAttackRelease(
                                        this.freqTable[midi],
                                        Math.max(0.01, dur),
                                        startTime,
                                        1.6 * velNorm
                                    );
                                }
                            }
                        }
                        this.lastPitchTriggerTimes[midi] = noteStart;
                        
                        // Only light keys that actually exist in the current keyboard range
                        const keyIdx = this.getKeyIndexForMidi(midi);
                        if (keyIdx !== null) {
                            this.keyExpirations[keyIdx] = noteStart + dur;
                            const hue = Math.floor(this.getHueForPacked(packed));
                            if (this.keyColorHues && keyIdx < this.keyColorHues.length) {
                                this.keyColorHues[keyIdx] = hue;
                            }
                        }
                        triggered++;
                    }
                }
            }
            this.audioPointer++;
        }
    }

    draw() {
        const ctx = this.ctx;
        const w = this.isExporting ? this.canvas.width : window.innerWidth;
        const h = this.isExporting ? this.canvas.height : window.innerHeight;

        // Clear background
        ctx.fillStyle = '#050505';
        ctx.fillRect(0, 0, w, h);

        let actualDrawCalls = 0;

        if (this.noteCount > 0 && this.noteChunks.length > 0) {
            const NPC = this.NOTES_PER_CHUNK;
            const playheadY = h - KEYBOARD_HEIGHT;
            const vs = this.visualSpeed || BASE_VISUAL_SPEED;

            if (this.renderQuality === 'absurd') {
                // Absurd renderer: draw ALL notes every frame, ignoring on-screen culling
                for (let i = 0; i < this.noteCount; i++) {
                    const cIdx = (i / NPC) | 0;
                    const iIdx = (i % NPC) * 3;
                    const chunk = this.noteChunks[cIdx];

                    const startTime = chunk[iIdx];
                    const dur = chunk[iIdx + 1];

                    let yBottom;
                    let yTop;

                    if (this.renderMode === 'real-tick' && this.pixelsPerTickBase > 0) {
                        const startTick = this.timeToTick(startTime);
                        const endTick = this.timeToTick(startTime + dur);
                        const pixelsPerTick = this.pixelsPerTickBase;
                        const relStartTick = startTick - this.currentTick;
                        yBottom = playheadY - relStartTick * pixelsPerTick;
                        yTop = yBottom - (endTick - startTick) * pixelsPerTick;
                    } else {
                        yBottom = playheadY - (startTime - this.currentTime) * vs;
                        yTop = yBottom - dur * vs;
                    }

                    const packed = this.noteChunksU32[cIdx][iIdx + 2];
                    const midi = packed & 0x1ff;
                    if (this.keyCount <= 0) continue;
                    const k = this.getKeyIndexForMidi(midi);
                    if (k === null) continue;

                    const hueIndex = Math.floor(this.getHueForPacked(packed)) % 360;
                    ctx.fillStyle = this.trackColorStrings[hueIndex];
                    const rectH = Math.max(1, yBottom - yTop);
                    ctx.fillRect(this.xOffsets[k], yTop, this.drawWidth, rectH);
                    actualDrawCalls++;
                }
            } else {
                // Update view indices every frame for maximum responsiveness
                this.cachedStartIdx = this.findNearestIndex(this.currentTime - this.maxNoteDuration);
                this.cachedEndIdx = this.findNearestIndex(this.currentTime + VISUAL_LOOKAHEAD);

                const start = this.cachedStartIdx;
                const end = this.cachedEndIdx;

                if (this.renderQuality === 'optimized' || this.renderQuality === 'unnecessary') {
                    // 1. Bucket notes by hue (depends on color mode)
                    const activeHues = new Set();
                    for (let i = 0; i < 360; i++) {
                        this.buckets[i].length = 0;
                    }

                    for (let i = start; i < end; i++) {
                        const cIdx = (i / NPC) | 0;
                        const iIdx = (i % NPC) * 3;
                        const startTime = this.noteChunks[cIdx][iIdx];
                        const dur = this.noteChunks[cIdx][iIdx + 1];

                        let yBottom;
                        let yTop;

                        if (this.renderMode === 'real-tick' && this.pixelsPerTickBase > 0) {
                            // Real tick-based vertical placement (constant pixels-per-tick, tempo-independent)
                            const startTick = this.timeToTick(startTime);
                            const endTick = this.timeToTick(startTime + dur);
                            const pixelsPerTick = this.pixelsPerTickBase;
                            const relStartTick = startTick - this.currentTick;
                            yBottom = playheadY - relStartTick * pixelsPerTick;
                            yTop = yBottom - (endTick - startTick) * pixelsPerTick;
                        } else {
                            // Time-based and fake tick-based vertical placement (time domain)
                            yBottom = playheadY - (startTime - this.currentTime) * vs;
                            yTop = yBottom - dur * vs;
                        }

                        // Fast culling: in "unnecessary" mode, only draw when fully inside the screen
                        // and despawn exactly at the keyboard; otherwise use the original padded culling.
                        if (this.renderQuality === 'unnecessary') {
                            // Visible only when the note has fully emerged from the top
                            // and hasn't yet reached the keyboard line.
                            if (yTop < 0 || yBottom > playheadY) continue;
                        } else {
                            if (yTop > playheadY || yBottom < -10) continue;
                        }

                        const packed = this.noteChunksU32[cIdx][iIdx + 2];
                        const hueIndex = Math.floor(this.getHueForPacked(packed)) % 360;
                        this.buckets[hueIndex].push(i);
                        activeHues.add(hueIndex);
                    }

                    // Reuse float buffers so the merge test runs at full precision.
                    // Comparing truncated integers with a loose tolerance made adjacent/overlapping
                    // notes drop in and out of a single merged rect (a 1px seam flickering with
                    // motion). Working in floats makes each group's span stable and seam-less.
                    if (!this.lastYTopF || this.lastYTopF.length !== this.keyCount) {
                        this.lastYTopF = new Float64Array(this.keyCount);
                        this.lastYBottomF = new Float64Array(this.keyCount);
                    }
                    const NEG = -1e9;

                    // 2. Render each hue bucket with merging optimization.
                    // Iterate active hues in numeric order (NOT insertion order). Insertion
                    // order follows the scrolling window, so it silently changes frame to
                    // frame as notes cross the window's edges; with differently-colored
                    // overlapping tracks that made whichever hue was drawn last (and thus won
                    // on top) flip repeatedly = the flicker.
                    for (let hue = 0; hue < 360; hue++) {
                        if (!activeHues.has(hue)) continue;
                        const bucket = this.buckets[hue];
                        const blen = bucket.length;
                        if (blen === 0) continue;

                        ctx.fillStyle = this.trackColorStrings[hue];
                        this.lastYTopF.fill(NEG);
                        this.lastYBottomF.fill(NEG);

                        for (let j = 0; j < blen; j++) {
                            const i = bucket[j];
                            const cIdx = (i / NPC) | 0;
                            const iIdx = (i % NPC) * 3;
                            const chunk = this.noteChunks[cIdx];

                            const startTime = chunk[iIdx];
                            const dur = chunk[iIdx + 1];

                            let yBottom;
                            let yTop;

                            if (this.renderMode === 'real-tick' && this.pixelsPerTickBase > 0) {
                                const startTick = this.timeToTick(startTime);
                                const endTick = this.timeToTick(startTime + dur);
                                const pixelsPerTick = this.pixelsPerTickBase;
                                const relStartTick = startTick - this.currentTick;
                                yBottom = playheadY - relStartTick * pixelsPerTick;
                                yTop = yBottom - (endTick - startTick) * pixelsPerTick;
                            } else {
                                yBottom = playheadY - (startTime - this.currentTime) * vs;
                                yTop = yBottom - dur * vs;
                            }

                            const packed = this.noteChunksU32[cIdx][iIdx + 2];
                            const midi = packed & 0x1ff;
                            if (this.keyCount <= 0) continue;
                            const k = this.getKeyIndexForMidi(midi);
                            if (k === null) continue;

                            // Vertical merge per key/hue, decided in float space so the result is
                            // stable across frames. Notes that truly overlap (or meet) on the same
                            // column coalesce into a single bar covering their exact union.
                            if (this.lastYBottomF[k] !== NEG && yBottom >= this.lastYTopF[k]) {
                                this.lastYTopF[k] = Math.min(this.lastYTopF[k], yTop);
                            } else {
                                if (this.lastYBottomF[k] !== NEG) {
                                    const top = Math.floor(this.lastYTopF[k]);
                                    const bot = Math.floor(this.lastYBottomF[k]);
                                    ctx.fillRect(this.xOffsets[k], top, this.drawWidth, Math.max(1, bot - top));
                                    actualDrawCalls++;
                                }
                                this.lastYBottomF[k] = yBottom;
                                this.lastYTopF[k] = yTop;
                            }
                        }

                        // Final flush for this hue
                        for (let k = 0; k < this.keyCount; k++) {
                            if (this.lastYBottomF[k] !== NEG) {
                                const top = Math.floor(this.lastYTopF[k]);
                                const bot = Math.floor(this.lastYBottomF[k]);
                                ctx.fillRect(this.xOffsets[k], top, this.drawWidth, Math.max(1, bot - top));
                                actualDrawCalls++;
                            }
                        }
                    }
                } else {
                    // Strict renderer: draw every note as its own rectangle without merging
                    for (let i = start; i < end; i++) {
                        const cIdx = (i / NPC) | 0;
                        const iIdx = (i % NPC) * 3;
                        const chunk = this.noteChunks[cIdx];

                        const startTime = chunk[iIdx];
                        const dur = chunk[iIdx + 1];

                        let yBottom;
                        let yTop;

                        if (this.renderMode === 'real-tick' && this.pixelsPerTickBase > 0) {
                            const startTick = this.timeToTick(startTime);
                            const endTick = this.timeToTick(startTime + dur);
                            const pixelsPerTick = this.pixelsPerTickBase;
                            const relStartTick = startTick - this.currentTick;
                            yBottom = playheadY - relStartTick * pixelsPerTick;
                            yTop = yBottom - (endTick - startTick) * pixelsPerTick;
                        } else {
                            yBottom = playheadY - (startTime - this.currentTime) * vs;
                            yTop = yBottom - dur * vs;
                        }

                        // Fast culling
                        yBottom = yBottom | 0;
                        yTop = yTop | 0;
                        if (yTop > playheadY || yBottom < -10) continue;

                        const packed = this.noteChunksU32[cIdx][iIdx + 2];
                        const midi = packed & 0x1ff;
                        if (this.keyCount <= 0) continue;
                        const k = this.getKeyIndexForMidi(midi);
                        if (k === null) continue;

                        const hueIndex = Math.floor(this.getHueForPacked(packed)) % 360;
                        ctx.fillStyle = this.trackColorStrings[hueIndex];
                        const rectH = Math.max(1, yBottom - yTop);
                        ctx.fillRect(this.xOffsets[k], yTop, this.drawWidth, rectH);
                        actualDrawCalls++;
                    }
                }
            }
        }

        this.currentDrawCalls = actualDrawCalls;

        // Draw keyboard
        for (let i = 0; i < this.keyCount; i++) {
            const isBlack = [1, 3, 6, 8, 10].includes((i + this.midiStartNote) % 12);
            const active = this.keyExpirations[i] > this.currentTime;
            const x = i * this.keyWidth;

            if (active) {
                const hue =
                    this.keyColorHues && this.keyColorHues[i] >= 0
                        ? this.keyColorHues[i]
                        : 0;
                ctx.fillStyle = this.trackColorStrings[hue % 360];
            } else {
                ctx.fillStyle = isBlack ? '#111' : '#fff';
            }

            ctx.fillRect(x, h - KEYBOARD_HEIGHT, this.keyWidth - 1, KEYBOARD_HEIGHT);

            if (isBlack && !active) {
                ctx.fillStyle = '#000';
                ctx.fillRect(
                    x,
                    h - KEYBOARD_HEIGHT,
                    this.keyWidth - 1,
                    KEYBOARD_HEIGHT * 0.6
                );
            }
        }
    }

    getSecondsPerTick(timeSec) {
        if (!this.tempoMap || this.tempoMap.length === 0) return 0;
        // tempoMap is sorted by time; find last entry with time <= current
        let low = 0;
        let high = this.tempoMap.length - 1;
        let idx = 0;
        while (low <= high) {
            const mid = (low + high) >>> 1;
            if (this.tempoMap[mid].time <= timeSec) {
                idx = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        const entry = this.tempoMap[idx];
        return entry && entry.spq ? entry.spq : 0;
    }

    getCurrentBpm(timeSec) {
        if (!this.tempoMap || this.tempoMap.length === 0 || !this.division) return 0;
        // tempoMap is sorted by time; find last entry with time <= current
        let low = 0;
        let high = this.tempoMap.length - 1;
        let idx = 0;
        while (low <= high) {
            const mid = (low + high) >>> 1;
            if (this.tempoMap[mid].time <= timeSec) {
                idx = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        const entry = this.tempoMap[idx];
        if (!entry || !entry.spq) return 0;
        const bpm = entry.mspb ? 60 * 1000000 / entry.mspb : 60 / (entry.spq * this.division);
        return Number.isFinite(bpm) && bpm > 0 ? bpm : 0;
    }

    // Convert an absolute time (seconds) into an absolute tick position using the tempo map
    timeToTick(timeSec) {
        if (!this.tempoMap || this.tempoMap.length === 0) return 0;

        // Find the last tempo entry with time <= timeSec
        let low = 0;
        let high = this.tempoMap.length - 1;
        let idx = 0;
        while (low <= high) {
            const mid = (low + high) >>> 1;
            if (this.tempoMap[mid].time <= timeSec) {
                idx = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }

        const entry = this.tempoMap[idx];
        if (!entry || !entry.spq) return entry ? entry.ticks : 0;

        const dt = timeSec - entry.time;
        if (dt <= 0) return entry.ticks;
        // spq is seconds per tick, so ticks = dt / spq
        return entry.ticks + dt / entry.spq;
    }

    animate() {
        requestAnimationFrame(() => this.animate());
        if (this.isExporting) return; // Dedicated loop handles export

        const now = performance.now();
        let clampedDelta = 0;
        if (now - this.lastBucketTime > 100) {
            this.lastBucketIndex = (this.lastBucketIndex + 1) % 10;
            this.npsBuckets[this.lastBucketIndex] = 0;
            this.lastBucketTime = now;
        }
        if (this.isPlaying) {
            const delta = (now - this.lastUpdateTime) / 1000;
            clampedDelta = Math.min(0.1, delta);

            // Determine currentTime and manage prerendered audio sync
            const ac = Tone.getContext().rawContext;
            const nowAudio = ac.currentTime;
            let songNowFromAudio = this.currentTime;

            if (this.audioMode === 'prerendered' && this.playbackStartAudioTime > 0) {
                songNowFromAudio = this.playbackStartSongTime + (nowAudio - this.playbackStartAudioTime);
                this.currentTime = songNowFromAudio;
                this.lastUpdateTime = now;

                if (this.midiData) {
                    const curChunkIdx = Math.floor(this.currentTime / this.CHUNK_DURATION);
                    const nextChunkIdx = curChunkIdx + 1;

                    // Cleanup old chunks and sources
                    const scheduledIndices = Array.from(this.scheduledChunks.keys());
                    for (const idx of scheduledIndices) {
                        if (idx < curChunkIdx) {
                            const source = this.scheduledChunks.get(idx);
                            try {
                                source.onended = null;
                                source.stop();
                                source.disconnect();
                            } catch (e) {}
                            this.scheduledChunks.delete(idx);
                        }
                    }

                    // Render ahead
                    [curChunkIdx, nextChunkIdx].forEach(idx => {
                        if (idx * this.CHUNK_DURATION < this.midiData.duration && 
                            !this.renderedChunks.has(idx) && 
                            !this.renderingChunks.has(idx)) {
                            this.renderChunk(idx);
                        }
                    });

                    // Play current chunk
                    if (this.renderedChunks.has(curChunkIdx) && !this.scheduledChunks.has(curChunkIdx)) {
                        const { buffer, chunkStartTime, duration } = this.renderedChunks.get(curChunkIdx);
                        const source = ac.createBufferSource();
                        source.buffer = buffer;
                        Tone.connect(source, this.prerenderedEntry);

                        const offset = Math.max(0, songNowFromAudio - chunkStartTime);
                        if (offset < buffer.duration) {
                            source.start(nowAudio, offset, Math.max(0.001, duration - offset));
                            this.scheduledChunks.set(curChunkIdx, source);
                        }
                    }
                    
                    // Pre-schedule next chunk
                    if (this.renderedChunks.has(nextChunkIdx) && !this.scheduledChunks.has(nextChunkIdx)) {
                        const { buffer, chunkStartTime, duration } = this.renderedChunks.get(nextChunkIdx);
                        const source = ac.createBufferSource();
                        source.buffer = buffer;
                        Tone.connect(source, this.prerenderedEntry);

                        const chunkAudioStart = this.playbackStartAudioTime + (chunkStartTime - this.playbackStartSongTime);
                        const startTime = Math.max(nowAudio, chunkAudioStart);
                        const offset = Math.max(0, nowAudio > chunkAudioStart ? nowAudio - chunkAudioStart : 0);

                        if (offset < buffer.duration) {
                            source.start(startTime, offset, Math.max(0.001, duration - offset));
                            this.scheduledChunks.set(nextChunkIdx, source);
                        }
                    }
                }
            } else {
                this.currentTime += clampedDelta;
                this.lastUpdateTime = now;
            }

            // Advance tick cursor using current tempo (for both fake and real tick modes)
            if (this.renderMode !== 'time' && this.tempoMap && this.tempoMap.length > 0) {
                const secondsPerTick = this.getSecondsPerTick(this.currentTime);
                if (secondsPerTick > 0) {
                    const ticksPerSecond = 1 / secondsPerTick;
                    this.currentTick += ticksPerSecond * clampedDelta;
                }
            }

            this.updateAudio(Tone.now());
            if (this.midiData && this.currentTime > this.midiData.duration) this.resetPlayback();
        }

        // Update BPM and visual speed every frame
        const bpm = this.getCurrentBpm(this.currentTime);
        this.currentBpm = bpm;

        if (this.renderMode === 'fake-tick' && bpm > 0) {
            // Fake tick-based: higher BPM -> faster scroll; 120 BPM is the baseline
            this.visualSpeed = BASE_VISUAL_SPEED * (bpm / 120);
        } else {
            // Time-based and real tick-based both use the base time scroll speed
            this.visualSpeed = BASE_VISUAL_SPEED;
        }

        if (this.bpmCounterEl) {
            this.bpmCounterEl.textContent = bpm ? `${Math.round(bpm)} BPM` : `0 BPM`;
        }

        this.draw();
        this.frames++;
        if (now >= this.lastFpsTime + 500) {
            this.fpsElement.textContent = `${Math.round((this.frames * 1000) / (now - this.lastFpsTime))} FPS`;
            this.noteCounterEl.textContent = `${this.audioPointer} / ${this.noteCount} notes`;
            this.npsCounterEl.textContent = `${this.npsBuckets.reduce((a, b) => a + b, 0)} NPS`;
            if (document.getElementById('draw-counter')) {
                document.getElementById('draw-counter').textContent = `${this.currentDrawCalls || 0} Rects`;
            }
            document.getElementById('active-voices').textContent = `${this.synth.activeVoices} / ${MAX_VOICES} Voices`;
            this.frames = 0;
            this.lastFpsTime = now;
        }

        if (this.midiData) {
            const progress = (this.currentTime / this.midiData.duration) * 100;
            document.getElementById('progress-bar').style.width = `${progress}%`;
            if (this.isExporting) {
                document.getElementById('export-progress-text').textContent = `${Math.floor(progress)}%`;
                if (this.currentTime >= this.midiData.duration) {
                    this.stopVideoExport();
                }
            }
        }
    }
}

new MidiApp();
