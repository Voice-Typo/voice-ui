/**
 * pcm-worklet.js — 원본 Float32 PCM 을 인식 서버로 업스트림하기 위한 AudioWorkletProcessor
 *
 * 서버가 원격 호스팅되면서 더 이상 로컬 마이크를 직접 읽지 못하므로, 브라우저가 떠 온 원본
 * 샘플을 그대로 메인 스레드로 넘겨 WS 바이너리 프레임으로 올려 보낸다. MediaRecorder(손실 압축)는
 * 포먼트를 훼손하므로 쓰지 않는다 — voice_collector/public/recorder-worklet.js 와 같은 원칙.
 *
 * 렌더 쿼텀(128 샘플)마다 postMessage 하면 48kHz 기준 초당 375회로 과하므로, 약 20ms 분량으로
 * 모아 한 번에 보낸다(zero-copy transfer). 어떤 필터링·게인·정규화도 적용하지 않는다.
 *
 * rms 는 업로드 배치와 별도로 480샘플(48kHz 기준 10ms) 블록마다 계산해 보낸다 — 서버
 * (recognizer/runtime.py:557, `np.sqrt(np.mean(hop*hop)+_EPS)`, hop=480샘플 원본 PCM)와
 * 같은 분해도를 로컬(지연 0)에서 재현하기 위함. 20ms 업로드 배치 그대로 쓰면 분해도가
 * 절반으로 떨어져 RELEASE_RATIO/DIP_MS(48ms) 재타격 판정이 보는 골이 창 평균에 묻힌다.
 */
class PcmSenderProcessor extends AudioWorkletProcessor {
  constructor(){
    super();
    this._blockSize = Math.max(128, Math.round(sampleRate*0.02));   // ~20ms (WS 업로드 배치)
    this._buf = new Float32Array(this._blockSize);
    this._n = 0;
    this._rmsBlockSize = Math.max(1, Math.round(sampleRate*0.01));  // ~10ms (서버 hop 과 동일 그리드)
    this._rmsSum = 0;
    this._rmsN = 0;
  }
  process(inputs){
    const input = inputs[0];
    if(!input || input.length === 0) return true;
    const ch = input[0];
    if(!ch) return true;
    for(let i=0;i<ch.length;i++){
      const x = ch[i];
      this._buf[this._n++] = x;
      if(this._n === this._blockSize){
        this.port.postMessage(this._buf, [this._buf.buffer]);
        this._buf = new Float32Array(this._blockSize);
        this._n = 0;
      }
      // 원본(비보정) 신호 그대로 — ref_rms 나눗셈 없음, 서버 정의와 동일
      this._rmsSum += x*x;
      this._rmsN++;
      if(this._rmsN === this._rmsBlockSize){
        this.port.postMessage({rms: Math.sqrt(this._rmsSum/this._rmsBlockSize)});
        this._rmsSum = 0;
        this._rmsN = 0;
      }
    }
    return true;
  }
}
registerProcessor('pcm-sender', PcmSenderProcessor);
