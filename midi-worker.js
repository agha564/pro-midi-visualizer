/**
 * Optimized MIDI Parser Worker
 * Handles massive files by using a single pass for tempo and note extraction,
 * and utilizes TypedArrays for memory efficiency.
 */

let mergedNoteChunks = [];
let workerNotesPerChunk = 1000000;
let workerNoteCount = 0;
let workerTimeIndexTable = null;
let freqTable = new Float32Array(512);
for (let i = 0; i < 512; i++) {
    freqTable[i] = 440 * Math.pow(2, (i - 69) / 12);
}

// Optimization: Fast Sine Lookup Table
const SINE_TABLE_SIZE = 8192;
const SINE_TABLE = new Float32Array(SINE_TABLE_SIZE + 1);
for (let i = 0; i <= SINE_TABLE_SIZE; i++) {
    SINE_TABLE[i] = Math.sin((i / SINE_TABLE_SIZE) * Math.PI * 2);
}

/**
 * ByteReader: Efficient, chunked reading from a File object.
 * Prevents loading entire massive files into RAM at once.
 */
class ByteReader {
    constructor(file, start, end) {
        this.file = file;
        this.start = start;
        this.end = end;
        this.pos = start;
        this.buffer = null;
        this.bufferPos = 0;
        this.chunkSize = 1024 * 512; // 512KB window for balanced performance
    }

    async prepare(needed = 1) {
        if (this.pos >= this.end) return false;
        // If no buffer or current position is outside buffer or we need more bytes than remaining in buffer
        if (!this.buffer || this.pos < this.bufferPos || (this.pos + needed) > (this.bufferPos + this.buffer.length)) {
            const size = Math.min(this.chunkSize + needed, this.end - this.pos);
            const ab = await this.file.slice(this.pos, this.pos + size).arrayBuffer();
            this.buffer = new Uint8Array(ab);
            this.bufferPos = this.pos;
        }
        return true;
    }

    readByteSync() {
        if (this.pos >= this.end) return 0;
        return this.buffer[this.pos++ - this.bufferPos];
    }

    readVLQSync() {
        let value = 0;
        let b;
        let safety = 0;
        do {
            if (this.pos >= this.end) break;
            b = this.buffer[this.pos++ - this.bufferPos];
            value = (value << 7) | (b & 0x7f);
            if (++safety > 5) break; // MIDI VLQ max is usually 4-5 bytes
        } while (b & 0x80);
        return value;
    }

    skipSync(n) {
        this.pos = Math.min(this.end, this.pos + n);
    }
}

/**
 * TrackParser: Pulls notes from a specific MIDI track on-demand.
 * This allows multi-way merging without storing all notes of all tracks in RAM.
 */
class TrackParser {
    constructor(reader, trackIdx, tempoMap, division) {
        this.reader = reader;
        this.trackIdx = trackIdx;
        this.tempoMap = tempoMap;
        this.division = division;
        this.ticks = 0;
        this.runningStatus = 0;
        this.tempoPtr = 0;
        this.activeNotes = new Int32Array(512).fill(-1);
        this.activeVels = new Uint8Array(512);
        this.nextNote = null;
    }

    async fetchNext() {
        this.nextNote = null;
        while (this.reader.pos < this.reader.end) {
            // Ensure at least 8 bytes for a standard MIDI event header/body
            if (!await this.reader.prepare(8)) break;
            
            const delta = this.reader.readVLQSync();
            this.ticks += delta;
            
            let status = this.reader.readByteSync();
            if (status < 0x80) {
                status = this.runningStatus;
                this.reader.pos--; 
            } else if (status < 0xF0) {
                this.runningStatus = status;
            }

            const type = status & 0xf0;
            if (type === 0x90 || type === 0x80) {
                const channel = status & 0x0f;
                const note = this.reader.readByteSync();
                const vel = this.reader.readByteSync();
                const safeNote = Math.max(0, Math.min(note, 511));

                if (type === 0x90 && vel > 0) {
                    this.activeNotes[safeNote] = this.ticks;
                    this.activeVels[safeNote] = vel & 0x7f;
                } else if (this.activeNotes[safeNote] !== -1) {
                    const startTick = this.activeNotes[safeNote];
                    const startVel = this.activeVels[safeNote];
                    this.activeNotes[safeNote] = -1;

                    // Compute time
                    while (this.tempoPtr + 1 < this.tempoMap.length && this.tempoMap[this.tempoPtr+1].ticks <= startTick) this.tempoPtr++;
                    const sTime = this.tempoMap[this.tempoPtr].time + (startTick - this.tempoMap[this.tempoPtr].ticks) * this.tempoMap[this.tempoPtr].spq;
                    
                    let endTempoPtr = this.tempoPtr;
                    while (endTempoPtr + 1 < this.tempoMap.length && this.tempoMap[endTempoPtr+1].ticks <= this.ticks) endTempoPtr++;
                    const eTime = this.tempoMap[endTempoPtr].time + (this.ticks - this.tempoMap[endTempoPtr].ticks) * this.tempoMap[endTempoPtr].spq;
                    
                    const dur = eTime - sTime;
                    const packed = (safeNote & 0x1FF) | (startVel << 9) | ((channel & 0x0F) << 16) | (this.trackIdx << 20);

                    this.nextNote = { time: sTime, dur, packed, startTick, ticks: this.ticks - startTick };
                    return true;
                }
            } else if (type === 0xa0 || type === 0xb0 || type === 0xe0) {
                this.reader.skipSync(2);
            } else if (type === 0xc0 || type === 0xd0) {
                this.reader.skipSync(1);
            } else if (status === 0xff) {
                this.reader.skipSync(1); // skip meta type
                const mLen = this.reader.readVLQSync();
                this.reader.skipSync(mLen);
            } else if (status === 0xf0 || status === 0xf7) {
                const sLen = this.reader.readVLQSync();
                this.reader.skipSync(sLen);
            }
        }
        return false;
    }
}

self.onmessage = async (e) => {
    const { file, type, chunkIdx, chunkDuration, sampleRate, myMidiId } = e.data;

    if (type === 'render-chunk') {
        renderAudioChunk(chunkIdx, chunkDuration, sampleRate, myMidiId, e.data.noteData);
        return;
    }

    if (type === 'render-full') {
        mergedNoteChunks = e.data.noteChunks;
        workerNotesPerChunk = e.data.notesPerChunk;
        workerNoteCount = e.data.noteCount;
        
        // Rebuild indexing for full render
        const lastChunk = mergedNoteChunks[mergedNoteChunks.length-1];
        const lastTime = lastChunk[lastChunk.length-3] || 0;
        const tableDensity = 5;
        const tableSize = Math.ceil((lastTime + 10) * tableDensity);
        workerTimeIndexTable = new Uint32Array(tableSize);
        let cur = 0;
        for (let i = 0; i < tableSize; i++) {
            const t = i / tableDensity;
            while (cur < workerNoteCount) {
                const cIdx = (cur / workerNotesPerChunk) | 0;
                const iIdx = (cur % workerNotesPerChunk) * 3;
                if (mergedNoteChunks[cIdx][iIdx] >= t) break;
                cur++;
            }
            workerTimeIndexTable[i] = cur;
        }

        await renderFullAudio(sampleRate, myMidiId);
        mergedNoteChunks = [];
        workerTimeIndexTable = null;
        return;
    }

    try {
        const headerBuf = await file.slice(0, 14).arrayBuffer();
        const headerData = new Uint8Array(headerBuf);
        const trackCount = readUint16(headerData, 10);
        const division = readUint16(headerData, 12);

        self.postMessage({ type: 'progress', progress: 5, text: "Scanning Tracks...", subtext: "Locating track boundaries..." });

        const trackBounds = [];
        const tempoMap = [{ ticks: 0, time: 0, spq: 500000 / 1000000 / division, mspb: 500000 }];
        
        let currentFilePos = 14;
        for (let i = 0; i < trackCount; i++) {
            const trackHeaderBuf = await file.slice(currentFilePos, currentFilePos + 8).arrayBuffer();
            const trackHeader = new Uint8Array(trackHeaderBuf);
            if (trackHeader.length < 8) break;
            const len = readUint32(trackHeader, 4);
            const start = currentFilePos + 8;
            trackBounds.push({ start, end: start + len });

            // Tempo scan with ByteReader
            const reader = new ByteReader(file, start, start + len);
            let ticks = 0, runningStatus = 0;
            while (reader.pos < reader.end) {
                if (!await reader.prepare()) break;
                ticks += reader.readVLQSync();
                let status = reader.readByteSync();
                if (status < 0x80) { status = runningStatus; reader.pos--; }
                else runningStatus = status;

                const type = status & 0xf0;
                if (status === 0xff) {
                    const metaType = reader.readByteSync();
                    const metaLen = reader.readVLQSync();
                    if (metaType === 0x51) {
                        if (!await reader.prepare(3)) break;
                        const mspb = (reader.readByteSync() << 16) | (reader.readByteSync() << 8) | reader.readByteSync();
                        if (mspb > 0) {
                            tempoMap.push({ ticks, spq: mspb / 1000000 / division, mspb });
                        }
                        reader.pos -= 3;
                    }
                    reader.skipSync(metaLen);
                } else if (type === 0x80 || type === 0x90 || type === 0xa0 || type === 0xb0 || type === 0xe0) { reader.skipSync(2); }
                else if (type === 0xc0 || type === 0xd0) { reader.skipSync(1); }
                else if (status === 0xf0 || status === 0xf7) {
                    const sLen = reader.readVLQSync();
                    reader.skipSync(sLen);
                }
            }
            currentFilePos = start + len;
        }

        tempoMap.sort((a, b) => a.ticks - b.ticks);
        for (let i = 1; i < tempoMap.length; i++) {
            const prev = tempoMap[i - 1];
            tempoMap[i].time = prev.time + (tempoMap[i].ticks - prev.ticks) * prev.spq;
        }

        self.postMessage({ type: 'progress', progress: 20, text: "Merging Notes...", subtext: "Processing streams..." });

        const NOTES_PER_CHUNK = 1000000;
        const noteChunks = [];
        let currentChunk = new Float32Array(NOTES_PER_CHUNK * 3);
        let currentChunkU32 = new Uint32Array(currentChunk.buffer);
        let chunkPtr = 0;

        let totalMerged = 0;
        let lastTime = 0;
        let globalMaxDur = 0;
        let globalMinNote = 511;
        let globalMaxNote = 0;

        const heap = new MinHeap();
        for (let t = 0; t < trackBounds.length; t++) {
            const parser = new TrackParser(new ByteReader(file, trackBounds[t].start, trackBounds[t].end), t, tempoMap, division);
            if (await parser.fetchNext()) {
                heap.push({ time: parser.nextNote.time, parser });
            }
        }

        while (heap.size() > 0) {
            const node = heap.pop();
            const note = node.parser.nextNote;

            if (chunkPtr >= NOTES_PER_CHUNK) {
                noteChunks.push(currentChunk);
                currentChunk = new Float32Array(NOTES_PER_CHUNK * 3);
                currentChunkU32 = new Uint32Array(currentChunk.buffer);
                chunkPtr = 0;
            }

            const off = chunkPtr * 3;
            currentChunk[off] = note.time;
            currentChunk[off + 1] = note.dur;
            currentChunkU32[off + 2] = note.packed;

            if (note.dur > globalMaxDur) globalMaxDur = note.dur;
            const midi = note.packed & 0x1ff;
            if (midi < globalMinNote) globalMinNote = midi;
            if (midi > globalMaxNote) globalMaxNote = midi;

            lastTime = note.time;
            chunkPtr++;
            totalMerged++;

            if (await node.parser.fetchNext()) {
                node.time = node.parser.nextNote.time;
                heap.push(node);
            }

            if (totalMerged % 250000 === 0) {
                self.postMessage({ 
                    type: 'progress', progress: 20 + Math.min(75, (totalMerged / 1000000) * 2), 
                    text: "Merging Notes...", subtext: `${Math.floor(totalMerged / 1000)}k notes processed` 
                });
            }
        }

        if (chunkPtr > 0) {
            const finalChunk = new Float32Array(chunkPtr * 3);
            finalChunk.set(currentChunk.subarray(0, chunkPtr * 3));
            noteChunks.push(finalChunk);
        }

        mergedNoteChunks = noteChunks;
        workerNotesPerChunk = NOTES_PER_CHUNK;
        workerNoteCount = totalMerged;

        const tableDensity = 5;
        const tableSize = Math.ceil((lastTime + 10) * tableDensity);
        workerTimeIndexTable = new Uint32Array(tableSize);
        let cur = 0;
        for (let i = 0; i < tableSize; i++) {
            const t = i / tableDensity;
            while (cur < workerNoteCount) {
                const cIdx = (cur / workerNotesPerChunk) | 0;
                const iIdx = (cur % workerNotesPerChunk) * 3;
                if (mergedNoteChunks[cIdx][iIdx] >= t) break;
                cur++;
            }
            workerTimeIndexTable[i] = cur;
        }

        const transferList = noteChunks.map(c => c.buffer);
        self.postMessage({ 
            type: 'done', 
            noteChunks, notesPerChunk: NOTES_PER_CHUNK,
            trackCount, duration: lastTime + 2, maxNoteDuration: globalMaxDur,
            noteCount: totalMerged, tempoMap, division, minNote: globalMinNote, maxNote: globalMaxNote
        }, transferList);

        // Explicitly clear local references to avoid keeping data in Worker RAM
        mergedNoteChunks = [];
        workerTimeIndexTable = null;

    } catch (err) {
        self.postMessage({ type: 'error', error: err.message });
    }
};

/**
 * Fast Min-Heap for Priority Queue Merging
 */
class MinHeap {
    constructor() { this.heap = []; }
    size() { return this.heap.length; }
    push(node) {
        this.heap.push(node);
        this.bubbleUp(this.heap.length - 1);
    }
    pop() {
        if (this.heap.length === 0) return null;
        const top = this.heap[0];
        const last = this.heap.pop();
        if (this.heap.length > 0) {
            this.heap[0] = last;
            this.bubbleDown(0);
        }
        return top;
    }
    bubbleUp(index) {
        while (index > 0) {
            let parent = (index - 1) >> 1;
            if (this.heap[index].time >= this.heap[parent].time) break;
            const tmp = this.heap[index];
            this.heap[index] = this.heap[parent];
            this.heap[parent] = tmp;
            index = parent;
        }
    }
    bubbleDown(index) {
        const len = this.heap.length;
        while (true) {
            let left = (index << 1) + 1;
            let right = (index << 1) + 2;
            let smallest = index;
            if (left < len && this.heap[left].time < this.heap[smallest].time) smallest = left;
            if (right < len && this.heap[right].time < this.heap[smallest].time) smallest = right;
            if (smallest === index) break;
            const tmp = this.heap[index];
            this.heap[index] = this.heap[smallest];
            this.heap[smallest] = tmp;
            index = smallest;
        }
    }
}





function readUint32(data, offset) {
    return (data[offset] << 24) | (data[offset+1] << 16) | (data[offset+2] << 8) | data[offset+3];
}

function readUint16(data, offset) {
    return (data[offset] << 8) | data[offset+1];
}

/**
 * Fast lookup for note index by time in the worker
 */
function findNearestIndexInWorker(targetTime) {
    if (workerNoteCount === 0 || targetTime <= 0) return 0;
    if (!workerTimeIndexTable) return 0;
    const tableIdx = Math.max(0, Math.floor(targetTime * 5));
    if (tableIdx >= workerTimeIndexTable.length) return workerNoteCount;
    
    let low = workerTimeIndexTable[tableIdx];
    let high = (tableIdx + 1 < workerTimeIndexTable.length) ? workerTimeIndexTable[tableIdx + 1] : workerNoteCount - 1;
    
    while (low <= high) {
        const mid = (low + high) >>> 1;
        const cIdx = (mid / workerNotesPerChunk) | 0;
        const iIdx = (mid % workerNotesPerChunk) * 3;
        if (mergedNoteChunks[cIdx][iIdx] < targetTime) low = mid + 1;
        else high = mid - 1;
    }
    return low;
}

/**
 * Professional-grade Lookahead Limiter / Maximizer
 * Prevents clipping while boosting quiet sections.
 */
function applyLimiter(audioData, sampleRate, boost = 1.0) {
    const len = audioData.length;
    if (len === 0) return;

    const attack = Math.exp(-1 / (0.0005 * sampleRate)); // 0.5ms attack
    const release = Math.exp(-1 / (0.120 * sampleRate)); // 120ms release
    let env = 0;

    for (let i = 0; i < len; i++) {
        const input = audioData[i] * boost;
        const absIn = Math.abs(input);

        // Fast-attack, slow-release envelope follower
        if (absIn > env) {
            env = attack * (env - absIn) + absIn;
        } else {
            env = release * (env - absIn) + absIn;
        }

        // Apply gain reduction if envelope exceeds ceiling
        const ceiling = 0.98;
        let gr = 1.0;
        if (env > ceiling) {
            gr = ceiling / env;
        }

        audioData[i] = input * gr;
    }
}

function renderAudioChunk(chunkIdx, chunkDuration, sampleRate, myMidiId, noteData) {
    const baseStartTime = chunkIdx * chunkDuration;
    const baseEndTime = baseStartTime + chunkDuration;
    
    const length = Math.ceil(chunkDuration * sampleRate);
    const audioData = new Float32Array(length);

    const attack = 0.005;
    const release = 0.05;
    const VELOCITY_THRESHOLD = 25;

    const noteCount = noteData.length / 3;
    const noteDataU32 = new Uint32Array(noteData.buffer);

    for (let nIdx = 0; nIdx < noteCount; nIdx++) {
        const i = nIdx * 3;
        const noteStart = noteData[i];
        const dur = noteData[i + 1];
        
        if (noteStart + dur < baseStartTime) continue;
        if (noteStart > baseEndTime) continue;

        const packed = noteDataU32[i + 2];
        const midi = packed & 0x1FF;
        const velocity = (packed >> 9) & 0x7F;

        if (velocity >= VELOCITY_THRESHOLD && midi >= 0 && midi < freqTable.length) {
            const velNorm = velocity / 127;
            const freq = freqTable[midi];
            const noteAmp = Math.sqrt(velNorm) * 0.35;

            const relStart = Math.max(0, noteStart - baseStartTime);
            const relEnd = Math.min(relStart + dur + release, chunkDuration);

            const startSample = Math.floor(relStart * sampleRate);
            const endSample = Math.ceil(relEnd * sampleRate);

            for (let n = startSample; n < endSample; n++) {
                if (n < 0 || n >= length) continue;
                const tLocal = n / sampleRate;
                const tNote = tLocal - (noteStart - baseStartTime);
                if (tNote < 0) continue;

                let env = 1.0;
                if (tNote < attack) {
                    env = tNote / attack;
                } else if (tNote > dur) {
                    const tRel = tNote - dur;
                    if (tRel >= release) break;
                    env = 1.0 - tRel / release;
                }

                const phase = (freq * tNote) % 1.0;
                const lookupIdx = (phase * SINE_TABLE_SIZE) | 0;
                const sig = SINE_TABLE[lookupIdx] * noteAmp * env;
                audioData[n] += sig;
            }
        }
    }

    // Apply limiter with a moderate fixed boost for chunked playback
    applyLimiter(audioData, sampleRate, 1.5);

    self.postMessage({
        type: 'rendered-chunk',
        chunkIdx,
        audioData,
        myMidiId
    }, [audioData.buffer]);
}

async function renderFullAudio(sampleRate, myMidiId) {
    if (mergedNoteChunks.length === 0) return;

    let totalDuration = 0;
    for (let c = 0; c < mergedNoteChunks.length; c++) {
        const chunk = mergedNoteChunks[c];
        for (let i = 0; i < chunk.length; i += 3) {
            const end = chunk[i] + chunk[i + 1];
            if (end > totalDuration) totalDuration = end;
        }
    }
    totalDuration += 1.0;

    const length = Math.ceil(totalDuration * sampleRate);
    if (length > 500000000) {
        self.postMessage({ type: 'error', error: "MIDI too long for full render (max ~3 hours)." });
        return;
    }

    const audioData = new Float32Array(length);
    const attack = 0.005;
    const release = 0.05;
    const VELOCITY_THRESHOLD = 25;

    const totalNotes = mergedNoteChunks.reduce((acc, c) => acc + (c.length / 3), 0);
    let notesProcessed = 0;

    // We process in time-slices (blocks) to avoid blocking the worker indefinitely and provide better progress
    const BLOCK_SIZE_SEC = 5.0;
    const totalBlocks = Math.ceil(totalDuration / BLOCK_SIZE_SEC);

    for (let b = 0; b < totalBlocks; b++) {
        const blockStartTime = b * BLOCK_SIZE_SEC;
        const blockEndTime = blockStartTime + BLOCK_SIZE_SEC;

        // Yield every few blocks to let the message loop breathe
        if (b % 2 === 0) {
            self.postMessage({
                type: 'progress',
                progress: Math.round((b / totalBlocks) * 100),
                text: "Rendering Full Audio...",
                subtext: `Processing block ${b + 1} / ${totalBlocks}`
            });
            await new Promise(r => setTimeout(r, 0));
        }

        // Optimization: only iterate through relevant notes for this block using the time index
        const startIdx = findNearestIndexInWorker(blockStartTime - 20); // 20s overlap buffer
        const endIdx = findNearestIndexInWorker(blockEndTime);

        for (let nIdx = startIdx; nIdx < endIdx; nIdx++) {
            const c = (nIdx / workerNotesPerChunk) | 0;
            const i = (nIdx % workerNotesPerChunk) * 3;
            const chunk = mergedNoteChunks[c];
            const chunkU32 = new Uint32Array(chunk.buffer, chunk.byteOffset, chunk.length);

            const noteStart = chunk[i];
            const noteDur = chunk[i + 1];
            const noteEnd = noteStart + noteDur + release;

            if (noteEnd < blockStartTime || noteStart > blockEndTime) continue;

            const packed = chunkU32[i + 2];
            const midi = packed & 0x1FF;
            const velocity = (packed >> 9) & 0x7F;

            if (velocity >= VELOCITY_THRESHOLD && midi >= 0 && midi < freqTable.length) {
                const velNorm = velocity / 127;
                const freq = freqTable[midi];
                const noteAmp = Math.sqrt(velNorm) * 0.35;

                const renderStart = Math.max(blockStartTime, noteStart);
                const renderEnd = Math.min(blockEndTime, noteEnd);

                const startSample = Math.floor(renderStart * sampleRate);
                const endSample = Math.ceil(renderEnd * sampleRate);

                const invSampleRate = 1 / sampleRate;
                const invAttack = 1 / attack;
                const invRelease = 1 / release;

                for (let n = startSample; n < endSample; n++) {
                    const tNote = (n * invSampleRate) - noteStart;
                    if (tNote < 0) continue;

                    let env = 1.0;
                    if (tNote < attack) {
                        env = tNote * invAttack;
                    } else if (tNote > noteDur) {
                        const tRel = tNote - noteDur;
                        if (tRel >= release) continue;
                        env = 1.0 - tRel * invRelease;
                    }

                    const phase = (tNote * freq) % 1.0;
                    const lookupIdx = (phase * SINE_TABLE_SIZE) | 0;
                    audioData[n] += SINE_TABLE[lookupIdx] * noteAmp * env;
                }
            }
        }
    }

    // Final Limiter Pass
    let sumSq = 0;
    const step = Math.max(1, Math.floor(length / 20000));
    let count = 0;
    for (let i = 0; i < length; i += step) {
        sumSq += audioData[i] * audioData[i];
        count++;
    }
    const rms = Math.sqrt(sumSq / count);
    let targetBoost = 0.20 / (rms + 0.00001);
    targetBoost = Math.max(1.0, Math.min(15.0, targetBoost));
    applyLimiter(audioData, sampleRate, targetBoost);

    const transferList = [audioData.buffer];
    for (const c of mergedNoteChunks) transferList.push(c.buffer);

    self.postMessage({
        type: 'full-audio-done',
        audioData,
        myMidiId,
        noteChunks: mergedNoteChunks
    }, transferList);
}
