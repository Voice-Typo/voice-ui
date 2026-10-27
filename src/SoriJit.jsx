import React from 'react';
import './sorijit.css';

// ── Python 인식 서버(remark_ws_server2.py) 연결 설정 ──────────────────
// ws://localhost:8765 로 프레임 판정 {vowel, vowel_raw, margin, f0, rms} 수신.
// 신선한 WS 프레임이 있으면 모음/피치를 Python 모델 값으로 덮어쓰고,
// 끊기거나 오래되면(STALE) 브라우저 포먼트 분석으로 자동 복귀한다.

// WebSocket 주소 결정. 우선순위: ?ws 쿼리 > 환경변수 > 자동(https→wss, http→ws://localhost:8765)
// https 페이지는 ws:// 차단(혼합 콘텐츠), wss:// 필수. 같은 호스트 리버스프록시 배포는 별도 설정 불필요.
function resolveRecogWsUrl() {
  const params = new URLSearchParams(location.search);
  let url = params.get('ws') || import.meta.env.VITE_RECOG_WS_URL;

  if (!url) {
    url = location.protocol === 'https:' ? `wss://${location.host}` : 'ws://localhost:8765';
  }

  const key = params.get('key');
  if (key && !url.includes('key=')) {
    url += (url.includes('?') ? '&' : '?') + `key=${encodeURIComponent(key)}`;
  }

  return url;
}

const RECOG_WS_URL = resolveRecogWsUrl();
const RECOG_STALE_MS = 300;

// 원본 x-dc 컴포넌트의 props 기본값
export const DEFAULT_PROPS = {"showMeters": false, "showGraph": true, "genZone": 0.78};

// 'a:b;c:d' 형태의 인라인 스타일 문자열을 React style 객체로
function cssObj(s){
  const o = {};
  if(typeof s !== 'string') return s || o;
  for(const decl of s.split(/;(?![^(]*\))/)){
    const i = decl.indexOf(':'); if(i < 0) continue;
    const k = decl.slice(0,i).trim(), val = decl.slice(i+1).replace('!important','').trim();
    if(!k) continue;
    o[k.startsWith('--') ? k : k.replace(/-([a-z])/g,(_,ch)=>ch.toUpperCase())] = val;
  }
  return o;
}

export default class SoriJit extends React.Component {
  state = { running:false, err:'', level:0, pitch:0, dur:0, trem:0, vowel:'', voiced:false,
    menuOpen:false, sens:1.2, thresh:0.05, basePitch:190, calibrating:false,
    endHold:320, sizeMul:1, vowelTol:0.6, meters:true, graph:true, useRecogWS:true, recogStatus:'off', freeze:false,
    bgMode:'off', bgDepth:0, bgShift:0.45, render3d:true, gl3dStatus:'loading',   // bgShift: 배경과 발화색의 파장 간격   // bgDepth: 배경 진하기 (0 아주 연하게 … 1 원색)
    srWarn:'', recogRefF0:null };   // srWarn: AudioContext 샘플레이트가 48000 이 아닐 때의 경고 / recogRefF0: 서버 캘리브레이션이 돌려준 기준 피치
  canvasRef = React.createRef();
  graphRef = React.createRef();
  pitchGraphRef = React.createRef();
  bubbles = []; ghosts = []; parts = []; remnants = [];
  cur = null; pitchHist = []; wave = [];
  lastVoiceT = 0; lastMeterT = 0; smoothLvl = 0;
  smoothSize = 0; rawRms = 0; vpMin = 800;   // 크기 전용 세기(0~2, dB) / 화면 짧은 변(px)
  _pcmRms = null;   // 워크릿이 서버의 10ms 홉 그리드로 로컬 계산해 보내는 rms(가장 최근 값, 평균 아님). null 이면 워크릿 미가동 → analyser 로 대체
  smoothTrem = 0; lastGoodPitch = 0;
  tremF = 0; tremFHz = 6; tremS = 0; tremSHz = 1;   // 잔떨림/억양 흔들림 세기(0~1)와 빠르기(Hz), 부드럽게 따라간 값   // 움직임용 실시간 떨림 / f0 옥타브 방어용 직전 유효 피치
  DEBUG_TREM = false;   // 임시 진단 오버레이 (확인 후 제거)
  bgTone = 0; bgWeight = 0; bgT = 0;   // 배경 색조 상태 (버블7)
  VOWELS = [['아',800,1250],['에',530,1950],['이',300,2350],['오',450,820],['우',350,700],['으',380,1400],['어',620,1000]];

  componentDidMount(){
    const cv = this.canvasRef.current;
    this.ctx = cv.getContext('2d');
    this.onResize = ()=>{ cv.width = cv.clientWidth*devicePixelRatio; cv.height = cv.clientHeight*devicePixelRatio;
      this.vpMin = Math.min(cv.clientWidth, cv.clientHeight);
      if(this.bgCanvas){ this.bgCanvas.width = cv.width; this.bgCanvas.height = cv.height; }
      if(this.gl3d) this.gl3d.resize(cv.clientWidth, cv.clientHeight, devicePixelRatio); };
    this.onResize(); window.addEventListener('resize', this.onResize);
    // 캡처용: 고정(freeze) 모드일 때 버블을 마우스로 드래그해 위치를 임의로 조정
    this._dragBubble = null; this._dragOffX = 0; this._dragOffY = 0;
    const hitBubble = (mx,my)=>{
      for(let i=this.bubbles.length-1;i>=0;i--){
        const b = this.bubbles[i]; if(b.dead) continue;
        const rad = Math.max(18, this.bubbleW(b)/2*.85);
        const dx = mx-b.x, dy = my-b.y;
        if(dx*dx+dy*dy <= rad*rad) return b;
      }
      return null;
    };
    // 3D 렌더가 켜져 있을 때는 화면(장면)이 좌우로 뒤집혀 그려지므로(버블14: '오른쪽으로
    // 보이도록 반사'), 논리 좌표(b.x)와 실제 화면 x 는 서로 거울상이다. 드래그 좌표도 같이 뒤집어야 한다.
    const toLogicalXY = (clientX, clientY)=>{
      const rect = cv.getBoundingClientRect();
      const sx = clientX-rect.left, sy = clientY-rect.top;
      const lx = this.gl3dOn() ? (cv.clientWidth - sx) : sx;
      return [lx, sy];
    };
    this.onDragDown = (e)=>{
      if(!this.state.freeze) return;
      const [mx,my] = toLogicalXY(e.clientX, e.clientY);
      const hit = hitBubble(mx,my);
      if(hit){ this._dragBubble = hit; this._dragOffX = mx-hit.x; this._dragOffY = my-hit.y; cv.style.cursor='grabbing'; }
    };
    this.onDragMove = (e)=>{
      const [mx,my] = toLogicalXY(e.clientX, e.clientY);
      if(this._dragBubble){
        this._dragBubble.x = mx-this._dragOffX; this._dragBubble.y = my-this._dragOffY;
      } else if(this.state.freeze){
        cv.style.cursor = hitBubble(mx,my) ? 'grab' : 'default';
      }
    };
    this.onDragUp = ()=>{ this._dragBubble = null; if(cv) cv.style.cursor = this.state.freeze ? 'grab' : 'default'; };
    cv.addEventListener('mousedown', this.onDragDown);
    window.addEventListener('mousemove', this.onDragMove);
    window.addEventListener('mouseup', this.onDragUp);
    // 캔버스는 @font-face 를 알아서 기다려 주지 않는다. 첫 프레임부터
    // 둥근 글자가 나오도록 명시적으로 로드시킨다.
    if(document.fonts && document.fonts.load){
      document.fonts.load('700 40px RoundKR', '아에이오우으어0123456789').catch(()=>{});
      document.fonts.load('600 12px RoundKR', '버블생성공간부유음성인식대기높낮을때음기준Hz').catch(()=>{});
    }
    this.initShell();
    this.initGL3D();
    if(this.state.useRecogWS) this.connectRecogWS();
    this.raf = requestAnimationFrame(this.loop);
  }
  componentWillUnmount(){ cancelAnimationFrame(this.raf); if(this.gl3d) this.gl3d.dispose(); window.removeEventListener('resize', this.onResize);
    window.removeEventListener('mousemove', this.onDragMove); window.removeEventListener('mouseup', this.onDragUp);
    if(this.canvasRef.current) this.canvasRef.current.removeEventListener('mousedown', this.onDragDown);
    this.disconnectRecogWS(); if(this.ac) this.ac.close(); if(this.stream) this.stream.getTracks().forEach(t=>t.stop()); }

  genRatio(){ return this.props.genZone ?? 0.74; }

  // ══════════════════════════════════════════════════════════════════
  //  3D 렌더 층 (Three.js)
  //  2D 코드는 방울을 '그리는 척'만 하고, 그 좌표·반지름·음정색·발성 길이를
  //  여기서 받아 WebGL 로 넘긴다. 음성 분석·물리·충돌·수명·글자 회전은
  //  한 줄도 바뀌지 않는다(절대규칙 1·2). WebGL 이 없으면 원래 2D 로 그린다.
  //  층 순서: 배경 캔버스(공기·수면선) → WebGL(막대·방울) → 2D 캔버스(글자·게이지)
  // ══════════════════════════════════════════════════════════════════
  async initGL3D(){
    const RES = { lib:'/assets/58bef27f-87db-48a1-8c62-1f04d4e5bfaa.js', env:'/assets/06d1c89e-cc0b-4083-bd35-5f2d7227e58b.jpg', glb:'/assets/532bbe92-eec5-42bf-9036-ce339b3bf657.glb' };
    try{
      const cv = this.canvasRef.current, host = cv.parentElement;
      if(!window.WebGL2RenderingContext) throw new Error('WebGL2 없음');
      this.bgCanvas = document.createElement('canvas');
      this.bgCanvas.setAttribute('aria-hidden','true');
      this.bgCanvas.style.cssText = 'position:absolute;inset:0;width:100%;height:100%;display:block;pointer-events:none';
      const blobs = window.__resourceBlobs || {};
      const getBlob = async u => blobs[u] || (await fetch(u)).blob();
      if(!window.SorijitThree){
        await new Promise((ok, no)=>{ const sc = document.createElement('script'); sc.src = RES.lib; sc.onload = ok; sc.onerror = no; document.head.appendChild(sc); });
      }
      const gl = await window.SorijitThree.createBubbleGL({ container: host,
        envBlob: await getBlob(RES.env), glbBlob: await getBlob(RES.glb), maxDpr: 2 });
      host.insertBefore(gl.canvas, cv);
      host.insertBefore(this.bgCanvas, gl.canvas);
      host.insertBefore(gl.bgCanvas, this.bgCanvas);
      this.bgCtx = this.bgCanvas.getContext('2d');
      this.gl3d = gl; this.onResize();
      this.setState({ gl3dStatus:'ready' });
    }catch(e){
      console.warn('3D 렌더를 켜지 못해 2D 로 그립니다:', e);
      this.gl3d = null; this.setState({ gl3dStatus:'failed' });
    }
  }
  gl3dOn(){ return !!(this.gl3d && this.state.render3d); }
  gl3dCapture(ctx, x, y, r, ar, now, alpha, seed, tone){
    const m = ctx.getTransform(), dpr = devicePixelRatio;
    const p = m.transformPoint(new DOMPoint(x, y));
    const sx = Math.hypot(m.a, m.b)/dpr, sy = Math.hypot(m.c, m.d)/dpr;
    const rx = r/Math.sqrt(ar)*sx, ry = r*Math.sqrt(ar)*sy;
    if(!(rx > 0.5) || !(ry > 0.5)) return;
    const fill = Math.max(0, Math.min(1, alpha));
    const dens = 0.50 + 0.50*Math.pow(fill, 1.15);        // 발성 길이 → 막의 농도 (2D 와 같은 자) — 짧은 소리는 더 투명하게
    const owner = this._gl3dOwner;
    // 막은 시간이 갈수록 얇아진다: 떠오른 방울은 회전이 멎어 갈수록(spinK→0),
    // 잔해 기포는 수명이 다해 갈수록. 얇아진 막은 금빛 → 푸른빛 → 정수리부터 검게 비친다.
    let life = 1;
    if(owner && owner.spinK !== undefined) life = owner.spinK;
    else if(owner && owner.life && owner.born) life = Math.max(0, 1 - (now - owner.born)/owner.life);
    const sd = seed || 0;
    const thick = (330 + 190*(0.5 + 0.5*Math.sin(sd*12.9898 + 1.3)))*(0.45 + 0.55*Math.pow(life, 0.55));
    const tc = (tone !== null && tone !== undefined)
      ? this.famPale(Math.max(-1, Math.min(1, tone)), 0.22).map(v=>v/255) : null;
    const gz = this._glFormZ || (owner && owner.gz ? owner.gz*Math.exp(-(now - owner.born)/260) : 0);
    const inst = { x:p.x/dpr, y:p.y/dpr, z:gz, rx, ry, seed:sd, thick, inten: dens*ctx.globalAlpha, tone:tc, toneAmt:1.0, milk: Math.pow(fill, 1.8) };   // 짧은 소리는 거의 맑게, 길수록 희뿌옇게 (차이를 벌림)
    this.gl3d.bubble(inst);
    if(owner){ let L = this._glFrame.get(owner); if(!L){ L = []; this._glFrame.set(owner, L); } L.push(inst); }
    const at = this.soapAttachment;
    if(at) this.gl3d.neck(inst, Math.max(0, Math.min(1, at.progress || 0)),this._wandGLFrame);
  }
  gl3dPopOwner(owner){
    if(!this.gl3d || !owner) return;
    const L = (this._glFrame && this._glFrame.get(owner)) || (this._glPrev && this._glPrev.get(owner));
    if(L) L.forEach(i=>this.gl3d.pop(i));
  }
  drawBgSource(ctx, W, H, now){
  const gy = H*this.genRatio();

  // ─────────────────────────────────────
  // 새 UI 배경
  // 기존 음성/버블 수치는 전혀 건드리지 않고
  // 캔버스의 명도 표현만 변경한다.
  // ─────────────────────────────────────
  const bd = this.state.bgDepth;

  if(this._glCap){
    // 3D 렌더러가 지원하는 경우 배경 깊이만 전달
    if(this.gl3d && this.gl3d.depth){
      this.gl3d.depth(bd);
    }
  } else if(bd > 0.005){
    // 2D fallback
    ctx.save();
    ctx.fillStyle = 'rgba(0,0,0,' + (bd*0.55).toFixed(3) + ')';
    ctx.fillRect(0,0,W,H);
    ctx.restore();
  }

  // 음정에 따른 배경 반응
  this.drawBgWash(ctx,W,H,now);

  // 생성공간 경계선
  ctx.save();

  const gl = ctx.createLinearGradient(0,0,W,0);
  gl.addColorStop(0,'rgba(255,255,255,0)');
  gl.addColorStop(.12,'rgba(255,255,255,.22)');
  gl.addColorStop(.5,'rgba(255,255,255,.30)');
  gl.addColorStop(.88,'rgba(255,255,255,.22)');
  gl.addColorStop(1,'rgba(255,255,255,0)');

  ctx.fillStyle = gl;
  ctx.fillRect(0,gy,W,1);

  const gw = ctx.createLinearGradient(0,0,W,0);
  gw.addColorStop(0,'rgba(255,255,255,0)');
  gw.addColorStop(.5,'rgba(255,255,255,.22)');
  gw.addColorStop(1,'rgba(255,255,255,0)');

  ctx.fillStyle = gw;
  ctx.fillRect(0,gy+1,W,1.4);

  ctx.font = '600 11.5px ' + this.UIFONT;
  ctx.fillStyle = 'rgba(255,255,255,.38)';

  ctx.textAlign='right';
  ctx.fillText('버블 생성 공간',W-56,gy+25);

  ctx.textAlign='left';
  ctx.fillText('부유 공간',56,gy-14);

  for(const rx of [36,W-36]){
    ctx.fillStyle='rgba(255,255,255,.40)';
    ctx.beginPath();
    ctx.arc(rx,gy+.5,2.6,0,Math.PI*2);
    ctx.fill();
  }

  ctx.restore();
}


  startDemo = ()=>{ this.demo = true; this.dm = null; this.setState({running:true, err:''}); };

  demoSample(now){
    if(!this.dm || now > this.dm.tEnd + this.dm.gap){
      const VS = this.VOWELS.map(v=>v[0]);
      const pick = ()=> Math.random()<0.16 ? null : VS[Math.floor(Math.random()*VS.length)];
      const r0 = Math.random();
      const nSeg = r0<0.18 ? 3 : r0<0.28 ? 4 : r0<0.55 ? 2 : 1; // 모음 3~4개 발화 포함
      const t0 = now, segs = []; let t = t0;
      const basePitch = 140+Math.random()*150;
      for(let i=0;i<nSeg;i++){
        const dur = 700+Math.random()*1600;
        segs.push({ v: pick(), t0:t, t1:t+dur,
          amp: .15+Math.random()*.6,
          pitch: basePitch + (Math.random()-.5)*60 });
        t += dur;
      }
      this.dm = { t0, segs, tEnd:t, gap: 900+Math.random()*1800, trem: Math.random()<0.3 };
    }
    const d = this.dm;
    if(now >= d.tEnd) return {level:0, pitch:-1, vowel:null};
    const seg = d.segs.find(s=>now>=s.t0 && now<s.t1) || d.segs[d.segs.length-1];
    const env = Math.min(1,(now-seg.t0)/180) * Math.min(1,(seg.t1-now)/220);
    const level = Math.min(1, seg.amp * (0.88+0.12*Math.sin(now/270)) * env + .01);
    const pitch = seg.pitch + (d.trem ? Math.sin(now/55)*seg.pitch*.05 : Math.sin(now/500)*4);
    return {level, pitch, vowel: seg.v};
  }

  // ── Python 인식 서버(remark_ws_server2.py) WebSocket 소스 ─────────────
  // ws://localhost:8765 에서 {vowel, vowel_raw, margin, f0, rms} 를 받는다.
  // vowel 은 '아'..'어' | '?' | null. '?'·null 은 '인식 안 됨' → null.
  // 음성 분석·물리·충돌·수명·글자 회전은 건드리지 않는다(절대규칙). loop 는
  // 신선한 WS 프레임이 있을 때만 모음·피치를 이 값으로 바꾸고, 없으면 포먼트로 복귀.
  connectRecogWS(){
    if(this.ws || !this.state.useRecogWS) return;
    this.setState({recogStatus:'connecting'});
    let ws;
    try{ ws = new WebSocket(RECOG_WS_URL); }
    catch(e){ this._scheduleRecogReconnect(); return; }
    this.ws = ws;
    ws.onopen = ()=>{ if(this.ws === ws) this.setState({recogStatus:'live'}); };
    ws.onmessage = (ev)=>{
      let d; try{ d = JSON.parse(ev.data); }catch(_){ return; }
      // 'hop' 이 아닌 제어 응답(calibrated/error/reset_ok)은 모음 판정 프레임이 아니므로 wsFrame 을
      // 건드리지 않고 여기서 처리만 한다 — 안 그러면 calibrated 응답이 vowel:null 로 잡혀 버블이 한 프레임 사라진다.
      if(d.type && d.type !== 'hop'){
        if(d.type === 'calibrated') this.setState({recogRefF0:(d.ref_f0 == null ? null : +d.ref_f0)});
        else if(d.type === 'error') console.error('[recogWS] 서버 오류:', d.message);
        // reset_ok 는 별도 처리 없음
        return;
      }
      const vw = (d.vowel === '?' || d.vowel == null) ? null : d.vowel;
      this.wsFrame = { vowel:vw,
        f0:(d.f0 == null ? null : +d.f0),
        // rms 는 저장만 해두고 세기(this.rawRms)에는 쓰지 않는다 — rms 는 의도적으로 로컬에서
        // (pcm-worklet.js, 서버와 같은 10ms 홉 그리드로) 계산한다. 지연 0 을 지키기 위함이니,
        // 이 필드를 "안 쓰고 있네" 하고 되살려 다시 연결하지 말 것.
        rms:(d.rms == null ? null : +d.rms),
        margin:(d.margin == null ? 0 : +d.margin),
        t:performance.now() };
    };
    ws.onerror = ()=>{};               // 정리는 onclose 에서
    ws.onclose = ()=>{
      if(this.ws === ws){ this.ws = null; this.wsFrame = null; }
      if(this.state.useRecogWS){ this.setState({recogStatus:'lost'}); this._scheduleRecogReconnect(); }
      else this.setState({recogStatus:'off'});
    };
  }
  _scheduleRecogReconnect(){
    if(this._wsRetry) return;
    this._wsRetry = setTimeout(()=>{ this._wsRetry = null;
      if(this.state.useRecogWS && !this.ws) this.connectRecogWS(); }, 2000);
  }
  disconnectRecogWS(){
    if(this._wsRetry){ clearTimeout(this._wsRetry); this._wsRetry = null; }
    const ws = this.ws; this.ws = null; this.wsFrame = null;
    if(ws){ ws.onclose = null; ws.onmessage = null; try{ ws.close(); }catch(_){} }
    this.setState({recogStatus:'off'});
  }
  recogFresh(now){ return !!(this.wsFrame && (now - this.wsFrame.t) < RECOG_STALE_MS); }

  start = async ()=>{
    try{
      this.stream = await navigator.mediaDevices.getUserMedia({audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false,channelCount:1}});
      // RE:MARK 수집기(recorder.ts)와 동일한 검증 — 요청만으로는 부족하고 실제로 꺼졌는지 getSettings() 로 확인한다.
      const track = this.stream.getAudioTracks()[0];
      const ts = track ? track.getSettings() : {};
      if(ts.echoCancellation !== false || ts.noiseSuppression !== false || ts.autoGainControl !== false){
        console.warn('[mic] echoCancellation/noiseSuppression/autoGainControl 이 꺼진 것으로 확인되지 않음 (포먼트 훼손 위험):', ts);
      }
      this.ac = new AudioContext({sampleRate:48000});
      // 샘플레이트는 요청만 가능하고 브라우저가 무시할 수 있다. 서버는 48kHz 를 가정하므로
      // 실제 값이 다르면 리샘플링 없이 조용히 보내지 않고(이 범위 밖) 경고로 드러낸다 —
      // 이 프로젝트에 "정규화 불일치로 인식률이 95%→30%로 붕괴"한 전례가 있어 조용한 성능 저하를 남기지 않는다.
      if(this.ac.sampleRate !== 48000){
        console.warn('[mic] AudioContext sampleRate가 48000Hz 가 아님:', this.ac.sampleRate);
        this.setState({srWarn:`⚠ 마이크 실제 샘플레이트 ${this.ac.sampleRate}Hz (서버는 48000Hz 가정 — 인식 품질 저하 가능)`});
      } else this.setState({srWarn:''});
      const src = this.ac.createMediaStreamSource(this.stream);
      this.an = this.ac.createAnalyser(); this.an.fftSize = 4096; this.an.smoothingTimeConstant = .5;
      src.connect(this.an);
      this.tbuf = new Float32Array(this.an.fftSize);
      this.fbuf = new Float32Array(this.an.frequencyBinCount);
      // ── 서버로 원본 PCM 업스트림 (AudioWorklet) ── 서버가 원격 호스팅되어 더 이상 로컬 마이크를
      // 직접 읽지 못하므로, 브라우저가 떠 온 샘플을 WS 바이너리 프레임으로 그대로 올려 보낸다.
      // MediaRecorder 는 손실 압축으로 포먼트를 훼손하므로 쓰지 않는다(recorder.ts 와 동일 원칙).
      try{
        await this.ac.audioWorklet.addModule('/pcm-worklet.js');
        this.pcmNode = new AudioWorkletNode(this.ac, 'pcm-sender', {numberOfInputs:1, numberOfOutputs:1, channelCount:1, channelCountMode:'explicit'});
        this.pcmNode.port.onmessage = (ev)=>{
          const d = ev.data;
          if(d instanceof Float32Array){
            if(this.ws && this.ws.readyState === WebSocket.OPEN) this.ws.send(d.buffer);
          } else if(d && typeof d.rms === 'number'){
            // 서버와 같은 10ms 홉 그리드의 로컬 rms. 애니메이션 프레임(~16.7ms)보다 자주 오므로
            // 가장 최근 값으로 덮어쓴다 — 평균하면 DIP_MS(48ms) 재타격 판정이 보는 골이 다시 뭉개진다.
            this._pcmRms = d.rms;
          }
        };
        src.connect(this.pcmNode);
        // Chrome 은 destination 까지 연결돼야 그래프를 구동한다. 게인 0 으로 물려 소리는 내지 않는다(하울링 방지).
        const sink = this.ac.createGain(); sink.gain.value = 0;
        this.pcmNode.connect(sink); sink.connect(this.ac.destination);
        this.pcmSink = sink;
      }catch(e){ console.error('[mic] PCM 업스트림 워크릿 로드 실패 — 인식 서버로 오디오가 전송되지 않습니다:', e); }
      this.setState({running:true, err:''});
    }catch(e){ this.setState({err:'마이크 권한이 필요합니다. 브라우저 설정에서 허용해 주세요.'}); }
  };

  autoCorrelate(buf, sr){
    let n = buf.length, rms = 0;
    for(let i=0;i<n;i++) rms += buf[i]*buf[i];
    rms = Math.sqrt(rms/n);
    if(rms < 0.004) return {pitch:-1, rms};
    let r1=0, r2=n-1, th=0.2;
    for(let i=0;i<n/2;i++) if(Math.abs(buf[i])<th){ r1=i; break; }
    for(let i=1;i<n/2;i++) if(Math.abs(buf[n-i])<th){ r2=n-i; break; }
    const b = buf.slice(r1,r2); n = b.length;
    if(n<64) return {pitch:-1, rms};
    const c = new Float32Array(n);
    for(let lag=0;lag<n;lag++){ let s=0; for(let i=0;i<n-lag;i++) s += b[i]*b[i+lag]; c[lag]=s; }
    let d=0; while(d<n-1 && c[d]>c[d+1]) d++;
    let maxv=-1, maxp=-1;
    for(let i=d;i<n;i++) if(c[i]>maxv){ maxv=c[i]; maxp=i; }
    if(maxp<=0 || maxv < 0.3*c[0]) return {pitch:-1, rms};
    let T = maxp;
    const x1=c[maxp-1]||0, x2=c[maxp], x3=c[maxp+1]||0;
    const a=(x1+x3-2*x2)/2, bq=(x3-x1)/2;
    if(a) T = maxp - bq/(2*a);
    const p = sr/T;
    return {pitch:(p>60 && p<600)?p:-1, rms};
  }

  // ── 재타격 분절 · 떨림 상수/로직 (voicetypo_ui BubbleVoiceUI.jsx 에서 이식) ──
  RELEASE_RATIO = 0.68;   // 세그 피크 대비 이 비율 아래로 꺼지면 '골'
  DIP_MS = 48;            // 골이 이만큼(ms) 이어져야 재타격 인정 (비브라토 오분할 방지)
  PEND_N = 14;            // 모음 전환은 이만큼 연속돼야 인정 (약 230ms, 한 프레임 튐 무시)
  UNREC_MS = 1800;        // 발성 중 인식불가가 이만큼 지속되면 방울이 터짐
  MAX_FORM_MS = 9000;     // 형성이 이보다 길면 강제 확정 (판정 어긋나 붙잡힘 안전망)
  TREM_WIN_MS = 1600;     // 잔떨림 분석 창 (2Hz 도 3주기 넘게 들어가야 반복 검사를 통과한다)
  TREM_F_LO = 2.0; TREM_F_HI = 12; TREM_F_STEP = 0.5;    // 훑을 대역(Hz) — 2Hz 대의 느린 떨림 ~ 8~12Hz 잔떨림까지
  AMP_TREM_DB_FULL = 4;       // 세기 떨림: 추세 제거 후 ±4dB 로 출렁이면 1.0
  AMP_TREM_FLAT_DB = 0.3;
  AMP_TREM_TONALITY_MIN = 0.5;   // 세기는 느린 크레셴도·재타격(0.6Hz 등)이 새어 들어오므로 집중도 하한을 더 높게     // 세기 흔들림이 이보다 작으면 평탄으로 보고 0
  AMP_TREM_SKIP_MS = 250;     // 소리 시작 직후의 상승 구간은 떨림으로 오인하므로 기록하지 않는다
  ampHist = []; _ampT0 = 0;
  TREM_TONALITY_MIN = 0.45;   // 집중도 하한 (올리면 '진짜 떨림'만) — 억양 흔들림의 배음이 잔떨림으로 새지 않게
  // 억양 흔들림(느린 떨림): 음을 규칙적으로 오르내리는 것. 1초에 한 번 안팎이라 창을 길게 본다.
  TREM_SLOW_WIN_MS = 3000;    // 0.7Hz 도 2주기 넘게 들어가는 창
  TREM_SLOW_F_LO = 0.7; TREM_SLOW_F_HI = 1.9; TREM_SLOW_F_STEP = 0.1;
  TREM_SLOW_TONALITY_MIN = 0.5;
  // 떨림 = '일정 간격으로, 일정 횟수 이상' 반복되는 오르내림. 목소리가 한 번 확 바뀐 것은 떨림이 아니다.
  TREM_MIN_CYCLES = 3;        // 잔떨림: 창 안에서 최소 3번 왕복
  TREM_SLOW_MIN_CYCLES = 2;   // 억양 흔들림: 최소 2번 왕복
  TREM_REG_CV_MAX = 0.4;      // 오르내림 간격의 들쭉날쭉함(변동계수) 상한
  TREM_HYST = 0.35;           // 기준선 넘나듦 판정 여유폭(흔들림 rms 대비) — 잔잡음으로 횟수가 부풀지 않게
  TREM_SLOW_DEPTH_K = 14;     // ±1반음 억양 흔들림 ≈ 0.8
  // 떨림 → 방울 흔들림 폭(px). 억양 흔들림은 넓고 느린 사인, 잔떨림은 좁고 빠른 사인.
  TREM_SLOW_PX = 34; TREM_FAST_PX = 7;
  TREM_FAST_VIS_HZ_MAX = 7;   // 화면에서 너무 빠르면 떨림이 아니라 지글거림으로 보여 상한을 둔다
  TREM_DEPTH_K = 40;          // 변조 깊이 → 0~1 배율 (±0.3반음 잔떨림 ≈ 0.66, ±0.6반음 이상이면 1.0)
  lastPitchSrc = 0;

  // 떨림 공통 분석: 최소제곱 추세 제거 후 TREM_F_LO~HI 대역에서 가장 센 성분을 찾는다.
  // 통과하면 {best, rms, mean, ton, n}, 탈락하면 사유 문자열.
  tremorBand(h, key, flatMin, tonMin=this.TREM_TONALITY_MIN, lo=this.TREM_F_LO, hi=this.TREM_F_HI, step=this.TREM_F_STEP, win=this.TREM_WIN_MS, dropSlow=null, minCycles=this.TREM_MIN_CYCLES){
    const n = h.length;
    if(n < 12) return 'n<12 n='+n;
    const t0 = h[0].t;
    if(h[n-1].t - t0 < win*0.5) return 'win';   // 창이 덜 찼으면 판단 보류
    let sx=0, sy=0, sxx=0, sxy=0;
    const xs = new Array(n);
    for(let i=0;i<n;i++){
      const x = (h[i].t - t0)/1000, y = h[i][key];
      xs[i] = x; sx+=x; sy+=y; sxx+=x*x; sxy+=x*y;
    }
    const mean = sy/n;
    const den = n*sxx - sx*sx;
    const slope = den ? (n*sxy - sx*sy)/den : 0;
    const icpt = (sy - slope*sx)/n;
    const res = new Array(n);
    let ss = 0;
    for(let i=0;i<n;i++){ const r = h[i][key] - (icpt + slope*xs[i]); res[i]=r; }
    // 잔떨림을 볼 때는 억양 흔들림(느린 성분)을 먼저 한 번 빼 둔다 — 억양과 잔떨림이 겹치면
    // 느린 성분이 흔들림의 대부분을 차지해 잔떨림의 집중도가 하한 밑으로 떨어지기 때문
    // dropSlow = 긴 창(3초)에서 이미 찾은 억양 흔들림 {hz, amp}. 짧은 창 안에서는 억양이 한 주기도
    // 안 들어갈 수 있어 주파수를 여기서 다시 찾지 않고 받아 쓴다.
    let slowAmp = 0, slowF = 0;
    if(dropSlow && dropSlow.hz > 0){
      const w = 2*Math.PI*dropSlow.hz;
      let re=0, im=0;
      for(let i=0;i<n;i++){ const a = w*xs[i]; re += res[i]*Math.cos(a); im += res[i]*Math.sin(a); }
      for(let i=0;i<n;i++){ const a = w*xs[i]; res[i] -= (2*re/n)*Math.cos(a) + (2*im/n)*Math.sin(a); }
      slowAmp = Math.max(dropSlow.amp || 0, 2*Math.hypot(re, im)/n); slowF = dropSlow.hz;
    }
    for(let i=0;i<n;i++) ss += res[i]*res[i];
    const rms = Math.sqrt(ss/n);
    if(rms < flatMin) return 'flat rms='+rms.toFixed(3)+' n='+n;
    let best = 0, bestF = 0;
    for(let f=lo; f<=hi+1e-9; f+=step){
      let re=0, im=0;
      const w = 2*Math.PI*f;
      for(let i=0;i<n;i++){ const a = w*xs[i]; re += res[i]*Math.cos(a); im += res[i]*Math.sin(a); }
      const mag = 2*Math.hypot(re, im)/n;
      if(mag > best){ best = mag; bestF = f; }
    }
    // 계단처럼 음을 오르내리는 억양은 3배·5배… 배음을 만든다. 잔떨림 후보가 억양의 정수배 자리에 있고
    // 세기도 배음 수준(억양/k)이면 잔떨림이 아니라 억양의 모양으로 본다.
    if(slowF > 0 && bestF > 0){
      const k = Math.round(bestF/slowF);
      if(k >= 2 && Math.abs(bestF - k*slowF) <= 0.2*k + 0.3 && best <= slowAmp/k*1.3) return 'harm k='+k;
    }
    const ton = Math.min(1, (best/Math.SQRT2)/rms);
    if(ton < tonMin) return 'ton<min ton='+ton.toFixed(2)+' best='+best.toFixed(1)+' n='+n;
    // 반복 검사: 흔들림이 기준선을 위아래로 넘나든 시점을 세어
    //  ① 최소 minCycles 번 왕복했는지 ② 간격이 고른지 ③ 그 간격이 찾은 주파수의 반주기와 맞는지 본다.
    //  (여유폭 TREM_HYST·rms 를 넘어야 넘나듦으로 친다 — 잔잡음 무시)
    //  세기 전에 찾은 주파수의 한 주기 길이 이동평균을 빼 둔다. 그 주파수의 흔들림은 그대로 남고,
    //  더 느린 출렁임(억양·덜 빠진 성분)과 계단은 사라져 넘나듦 간격이 흐트러지지 않는다.
    const half = 0.5/bestF, hp = new Array(n);
    let hs = 0;
    for(let i=0, lo=0, hi=0, sum=0; i<n; i++){
      while(hi < n && xs[hi] <= xs[i] + half){ sum += res[hi]; hi++; }
      while(xs[lo] < xs[i] - half){ sum -= res[lo]; lo++; }
      hp[i] = res[i] - sum/(hi - lo); hs += hp[i]*hp[i];
    }
    const hy = this.TREM_HYST*Math.sqrt(hs/n), flips = [];
    let side = 0;
    for(let i=0;i<n;i++){
      if(side <= 0 && hp[i] > hy){ if(side < 0) flips.push(xs[i]); side = 1; }
      else if(side >= 0 && hp[i] < -hy){ if(side > 0) flips.push(xs[i]); side = -1; }
    }
    const cyc = flips.length/2;
    if(cyc < minCycles) return 'cyc<min cyc='+cyc.toFixed(1)+' ton='+ton.toFixed(2);
    const gaps = []; for(let i=1;i<flips.length;i++) gaps.push(flips[i]-flips[i-1]);
    const gm = gaps.reduce((a,b)=>a+b,0)/gaps.length;
    const cv = Math.sqrt(gaps.reduce((a,g)=>a+(g-gm)*(g-gm),0)/gaps.length)/gm;
    if(cv > this.TREM_REG_CV_MAX) return 'irregular cv='+cv.toFixed(2)+' cyc='+cyc.toFixed(1);
    const ratio = (2*gm)*bestF;   // 센 주기 / 찾은 주기
    if(ratio < 0.6 || ratio > 1.6) return 'period≠f ratio='+ratio.toFixed(2);
    return {best, rms, mean, ton, n, hz: bestF, cyc};
  }
  // 음높이 잔떨림(2~12Hz): 최근 TREM_WIN_MS 의 f0 가 평균 대비 몇 % 로 규칙적으로 출렁이는가
  // 잔떨림은 끊기지 않고 이어진 마지막 구간에서만 본다. 무음으로 끊긴 조각·음 계단이 섞이면
  // 억양 흔들림이 2~3Hz 잔떨림으로 잘못 잡힌다.
  lastRun(h, maxGap=100){
    let i = h.length - 1;
    while(i > 0 && h[i].t - h[i-1].t <= maxGap) i--;
    return i > 0 ? h.slice(i) : h;
  }
  computeTremor(now, slow){
    const h = this.lastRun(this.pitchHist.filter(x=>now - x.t < this.TREM_WIN_MS));
    const r = this.tremorBand(h, 'p', 0.05, this.TREM_TONALITY_MIN, this.TREM_F_LO, this.TREM_F_HI, this.TREM_F_STEP, this.TREM_WIN_MS, slow);
    if(typeof r === 'string'){ this._td = 'f0 '+r; return {v:0, hz:0}; }
    if(!(r.mean > 0)) return {v:0, hz:0};
    const out = Math.min(1, (r.best/r.mean)*this.TREM_DEPTH_K);
    this._td = 'f0 ok out='+out.toFixed(2)+' '+r.hz+'Hz ton='+r.ton.toFixed(2)+' n='+r.n;
    return {v:out, hz:r.hz};
  }
  // 억양 흔들림(0.7~1.9Hz): 최근 TREM_SLOW_WIN_MS 동안 음을 규칙적으로 오르내리는가
  computeSlowTremor(){
    const r = this.tremorBand(this.pitchHist, 'p', 0.05, this.TREM_SLOW_TONALITY_MIN,
      this.TREM_SLOW_F_LO, this.TREM_SLOW_F_HI, this.TREM_SLOW_F_STEP, this.TREM_SLOW_WIN_MS*1.4, null, this.TREM_SLOW_MIN_CYCLES);
    if(typeof r === 'string'){ this._tds = 'slow '+r; return {v:0, hz:0}; }
    if(!(r.mean > 0)) return {v:0, hz:0};
    // 대역 윗끝에 걸린 것은 더 빠른 잔떨림(2Hz~)이 새어 든 것 — 잔떨림 쪽에 맡긴다
    if(r.hz >= this.TREM_SLOW_F_HI - 1e-6){ this._tds = 'slow edge '+r.hz.toFixed(1)+'Hz'; return {v:0, hz:0}; }
    const out = Math.min(1, (r.best/r.mean)*this.TREM_SLOW_DEPTH_K);
    this._tds = 'slow ok out='+out.toFixed(2)+' '+r.hz.toFixed(1)+'Hz ton='+r.ton.toFixed(2);
    return {v:out, hz:r.hz, amp:r.best};
  }
  // 세기 떨림: 잘리지 않은 원래 세기(dB)가 몇 dB 로 규칙적으로 출렁이는가
  computeAmpTremor(){
    const r = this.tremorBand(this.lastRun(this.ampHist), 'db', this.AMP_TREM_FLAT_DB, this.AMP_TREM_TONALITY_MIN);
    if(typeof r === 'string'){ this._tda = 'amp '+r; return {v:0, hz:0}; }
    const out = Math.min(1, r.best/this.AMP_TREM_DB_FULL);
    this._tda = 'amp ok out='+out.toFixed(2)+' '+r.hz+'Hz ton='+r.ton.toFixed(2)+' n='+r.n;
    return {v:out, hz:r.hz};
  }

  // ── dB 크기 매핑 (voicetypo_ui 에서 이식) : 선형 rms 는 웬만한 발성이 다 최대로 클립됐다 ──
  SIZE_DB_LO = -50; SIZE_DB_HI = -18; SIZE_DB_HEAD = 12;   // dB 구간 (속삭임~또렷~절대최대)
  SIZE_R_MIN = 10; SIZE_R_NOM = 70; SIZE_FILL = 0.22; SIZE_GAMMA = 1.0;
  // SIZE_FILL: 헤드룸(-18dBFS 초과) 구간에서 방울이 커질 수 있는 상한을 화면 짧은 변 대비 비율로 정한다.
  // 0.44 였을 때 1080 화면에서 반지름 475px(지름 950px)까지 커져 여러 개가 뜨면 화면이 막혔다.
  // 0.22 면 반지름 238px. 더 줄이려면 이 값만 낮추면 된다(0.15~0.25 사이에서 맞춰볼 것).
  LVL_ATTACK = 0.2;   // 크기 커질 때 추종
  LVL_RELEASE = 0;    // 줄어들 때 0 = 완전 피크 홀드

  // rms → 정규화 세기 (0~1 일상, 1~2 헤드룸)
  loudNorm(rms){
    const L = 20*Math.log10(Math.max(rms, 1e-7));
    const t = (L - this.SIZE_DB_LO) / (this.SIZE_DB_HI - this.SIZE_DB_LO);
    if(t <= 1) return Math.max(0, t);
    return 1 + Math.min(1, (L - this.SIZE_DB_HI) / this.SIZE_DB_HEAD);
  }
  // 정규화 세기 → 반지름(px)
  segRadius(lvl){
    const nom = Math.max(0, Math.min(1, lvl));
    let r = this.SIZE_R_MIN + (this.SIZE_R_NOM - this.SIZE_R_MIN) * Math.pow(nom, this.SIZE_GAMMA);
    if(lvl > 1){
      const u = Math.min(1, lvl - 1);
      const rMax = Math.max(this.SIZE_R_NOM, this.vpMin * this.SIZE_FILL);
      r += (rMax - this.SIZE_R_NOM) * u * u;
    }
    return r * this.state.sizeMul;
  }

  BLOW_HOLD_MS = 180;   // 이만큼 이어져야 입김(바람)으로 인정
  BLOW_GAIN = 1.3;      // 발성 문턱(thresh)의 몇 배 이상이어야 하나
  windK = 0;            // 현재 바람 세기 0~1
  BREATH_FLAT = 0.25;   // 부분대역 평탄도가 이보다 크면 입김(잡음)으로 본다. 합성 검증: 모음 ≤0.06, 입김 ≥0.34
  breathK = 0;

  CLAP_GAIN = 2.2;         // 발성 문턱 대비 최소 크기. 바람(1.3)보다 높게 잡아 오작동을 줄인다
  CLAP_RISE = 0.18;        // 직전 프레임 대비 level 상승폭. 박수는 어택이 급격하다
  CLAP_FLAT = 0.25;        // 평탄도. 박수는 충격음이라 배음 구조가 없다 (바람과 같은 기준)
  CLAP_COOLDOWN_MS = 600;  // 연타·반향으로 연달아 터지는 것을 막는다

  // 300~3000Hz 를 450Hz 폭으로 나눠 각 대역의 스펙트럼 평탄도(기하평균/산술평균)를 에너지 가중 평균.
  // 대역 폭이 배음 간격(f0 ≤ 300Hz)보다 넓어 모음은 봉우리 때문에 낮고, 잡음은 포먼트 모양이어도
  // 대역 안에선 평평해서 높다. 전 대역 한 번에 재면 '우' 모양 입김이 모음과 구분되지 않는다.
  breathiness(){
    const f = this.fbuf, binHz = this.ac.sampleRate/this.an.fftSize;
    let num = 0, den = 0;
    for(let lo=300; lo<3000; lo+=450){
      const i0 = Math.floor(lo/binHz), i1 = Math.floor((lo+450)/binHz);
      let lg = 0, ar = 0;
      for(let i=i0;i<i1;i++){ const p = Math.pow(10, (f[i] > -200 ? f[i] : -200)/10) + 1e-20; lg += Math.log(p); ar += p; }
      const n = i1 - i0, fl = Math.exp(lg/n)/(ar/n);
      num += fl*ar; den += ar;
    }
    return den > 0 ? num/den : 0;
  }

  classifyVowel(){
    const f = this.fbuf, sr = this.ac.sampleRate, binHz = sr/this.an.fftSize;
    const pow = i => Math.pow(10, (f[i]||-160)/20);
    const sm = i => { let s=0; for(let k=-2;k<=2;k++) s += pow(Math.max(0,i+k)); return s; };
    const peak = (lo,hi)=>{ let bi=-1,bv=0; const i0=Math.floor(lo/binHz), i1=Math.ceil(hi/binHz);
      for(let i=i0;i<=i1;i++){ const v=sm(i); if(v>bv && v>=sm(i-1) && v>=sm(i+1)){ bv=v; bi=i; } }
      return bi<0?-1:bi*binHz; };
    const F1 = peak(250,1000); if(F1<0) return null;
    const F2 = peak(Math.max(650,F1+180), 3000); if(F2<0) return null;
    let best=null, bd=1e9;
    for(const [v,p1,p2] of this.VOWELS){
      const d = Math.pow(Math.log(F1/p1),2)*1.4 + Math.pow(Math.log(F2/p2),2);
      if(d<bd){ bd=d; best=v; }
    }
    return bd < this.state.vowelTol ? best : null;
  }

  loop = ()=>{
    this.raf = requestAnimationFrame(this.loop);
    const cv = this.canvasRef.current; if(!cv) return;
    const ctx = this.ctx, W = cv.width/devicePixelRatio, H = cv.height/devicePixelRatio;
    ctx.setTransform(devicePixelRatio,0,0,devicePixelRatio,0,0);
    ctx.clearRect(0,0,W,H);
    const now = performance.now();
    // 프레임 간격 — 감속·추종처럼 '초당' 으로 정의된 값들이 모두 이걸 쓴다
    const dt = Math.min(64, now - (this.lastT || now)); this.lastT = now;
    this.stepBake();   // 박막 셸 스프라이트를 시간 예산 안에서 이어 굽는다

    let level=0, pitch=-1, vowel=null, trem=0, demoV=null;
    if(this.state.running && (this.an || this.demo)){
      if(this.demo){
        const r = this.demoSample(now);
        level = r.level; pitch = r.pitch; demoV = r.vowel;
      } else {
      this.an.getFloatTimeDomainData(this.tbuf);
      this.an.getFloatFrequencyData(this.fbuf);
      const r = this.autoCorrelate(this.tbuf, this.ac.sampleRate);
      pitch = r.pitch;
      // 세기(rms)는 로컬에서, 서버와 같은 10ms 홉 그리드로 계산한다(pcm-worklet.js, this._pcmRms).
      // 지연·분해도는 별개 문제였다: 지연은 로컬이라 왕복 0 으로 이미 최선이고, 분해도는
      // AnalyserNode(fftSize 4096 ≈ 85ms@48kHz)가 문제였다 — RELEASE_RATIO/DIP_MS(48ms) 재타격
      // 판정이 봐야 할 골을 85ms 창 평균이 묻어버려, 분절이 그 임계값엔 너무 거친 신호로 구동됐다.
      // 워크릿이 10ms 블록 rms 를 로컬로 주므로 분해도도 고쳐지고 왕복은 여전히 없다.
      // 워크릿 로드 실패 시(this._pcmRms 가 한 번도 안 옴)에만 analyser 값으로 대체한다.
      this.rawRms = (this._pcmRms != null) ? this._pcmRms : r.rms;
      level = Math.min(1, this.rawRms*9*this.state.sens);
      // Python 인식 WS 가 신선하면 피치는 YIN(Python) 값 우선 (없으면 브라우저 autoCorrelate 유지)
      if(this.state.useRecogWS && this.recogFresh(now) && this.wsFrame.f0 != null) pitch = this.wsFrame.f0;
      // 입김 거부: 바람 소리의 저역 웅웅거림은 자기상관에 가짜 주기를 만들어 모음으로 새어 들어온다.
      // 부분대역 평탄도가 높으면(배음 봉우리 없는 잡음) 피치를 지우고 발성 여유(lastF0T)도 끊는다.
      // WS f0 덮어쓰기 뒤에 둬야 서버 쪽 가짜 f0 도 함께 막힌다.
      this.breathK += (this.breathiness() - this.breathK)*0.5;
      if(this.rawRms > 0.004 && this.breathK > this.BREATH_FLAT){ pitch = -1; this.lastF0T = -1e9; }
      }
      if(this.calibEnd){
        this.calibMax = Math.max(this.calibMax, level);
        if(now > this.calibEnd){
          const t = Math.min(.2, Math.max(.03, this.calibMax*1.8+.02));
          this.calibEnd = 0; this.setState({thresh:+t.toFixed(3), calibrating:false});
          // UI 캘리브레이션이 끝나는 순간 서버 캘리브레이션도 같이 끝낸다 — ref_rms/ref_f0 가
          // UI가 측정한 것과 같은 발화 구간에서 나오도록(calibrate_start 는 calibrateNoise() 에서 보냄).
          if(this.ws && this.ws.readyState === WebSocket.OPEN) this.ws.send(JSON.stringify({type:'calibrate_end'}));
        }
      }
      // 타자·박수 등 피치 없는 잡음 차단 — f0 가 있어야 발성으로 인정(250ms 여유)
      if(pitch>0) this.lastF0T = now;
      const voiced = level > this.state.thresh && !this.state.calibrating && (now - (this.lastF0T||-1e9) < 250);
      const _useWS = this.state.useRecogWS && !this.demo && this.recogFresh(now);
      if(voiced) vowel = this.demo ? demoV : (_useWS ? this.wsFrame.vowel : this.classifyVowel());
      // ── 바람(후~) 감지: 피치 없는 큰 소리가 BLOW_HOLD_MS 이상 이어지면 입김으로 본다 ──
      // 박수·타자는 짧아서 지속 조건에 걸러진다. 세기만큼 바람이 세지고(windK 0~1),
      // 방울은 drawSceneSource 에서 막대 고리 반대쪽으로 날려 화면 밖에서 사라진다.
      const breathy = !this.demo && !this.state.calibrating && pitch <= 0 && level > this.state.thresh*this.BLOW_GAIN;
      if(breathy){ if(!this._blowT0) this._blowT0 = now; } else this._blowT0 = 0;
      const blowing = breathy && now - this._blowT0 > this.BLOW_HOLD_MS;
      const windT = blowing ? Math.min(1, 0.45 + this.loudNorm(this.rawRms)*0.6) : 0;
      this.windK += (windT - this.windK)*Math.min(1, dt/(windT > this.windK ? 60 : 220));
      // ── 박수 감지: 짧고 크고 광대역이며 어택이 급격한 소리 ── 바람과 반대로 지속이 아니라
      // 직전 프레임 대비 급상승(CLAP_RISE)을 본다. 평탄도 기준(CLAP_FLAT)은 바람과 동일.
      // ⚠️ 문 닫는 소리·물건 떨어지는 소리·마이크를 건드리는 소리도 똑같이 걸린다 — 전시장에서
      // 오작동 소지가 있음. CLAP_GAIN(크기)·CLAP_RISE(어택 급격함)를 올리면 둔감(놓침↑, 오작동↓),
      // 내리면 민감(오작동↑, 놓침↓) — 현장에서 조정할 때는 이 둘을 건드릴 것.
      const prevLevel = this._prevLevel != null ? this._prevLevel : level;
      const isClap = !this.demo && !this.state.calibrating
        && level > this.state.thresh*this.CLAP_GAIN
        && (level - prevLevel) > this.CLAP_RISE
        && this.breathK > this.CLAP_FLAT
        && now - (this._lastClapT || -1e9) > this.CLAP_COOLDOWN_MS;
      if(isClap){
        this._lastClapT = now;
        // 한 번의 박수로 전부 같은 프레임에 터지면 오류처럼 보이므로 0~260ms 로 흩뜬다
        // (입김의 120~500ms 보다 좁게 — 박수는 순간적인 소리라 번지는 느낌도 더 짧아야 한다)
        for(const b of this.bubbles){ if(!b.dead && b.popAt === undefined) b.popAt = now + Math.random()*260; }
      }
      this._prevLevel = level;
      this.smoothLvl += (level - this.smoothLvl)*0.25;
      // 크기 전용 세기 — dB 로그 매핑(클리핑 없음). 미터·배경이 쓰는 smoothLvl 과 분리한다.
      const sizeRaw = this.demo ? Math.max(0, Math.min(1, level)) : this.loudNorm(this.rawRms);
      this.smoothSize += (sizeRaw - this.smoothSize)*0.25;

      // 기준음(색·회전의 0점)을 화자의 실제 음역 중심으로 천천히 옮긴다.
      // 발성 중에만 움직이고 τ≈8초라, 한 번의 발화 안에서는 사실상 고정이다.
      if(pitch>0 && level > this.state.thresh){
        if(!(this.pitchAvg>0)) this.pitchAvg = pitch;
        else this.pitchAvg += (pitch - this.pitchAvg)*Math.min(1, dt/1000*this.BASE_ADAPT);
        this.pitchAvg = Math.max(70, Math.min(400, this.pitchAvg));
      }
      // f0 표본 적재 — WS 모드에선 '새 프레임일 때만' 담는다 (같은 값 중복 적재 → 스펙트럼 왜곡 방지)
      if(pitch>0){
        const src = (this.state.useRecogWS && !this.demo && this.recogFresh(now)) ? this.wsFrame.t : now;
        if(src !== this.lastPitchSrc){
          this.lastPitchSrc = src;
          // f0 옥타브 오류(반값/배값) 방어 — 직전 유효값에서 4반음 넘게 튀면 떨림 계산에서 제외
          // (단, 2프레임 연속 벗어나면 진짜 음정 이동으로 보고 받아들여 영구 거부 방지)
          const lp = this.lastGoodPitch;
          if(!(lp>0) || Math.abs(Math.log2(pitch/lp))*12 < 4 || (this._pRej||0) >= 2){
            this.pitchHist.push({t:now,p:pitch}); this.lastGoodPitch = pitch; this._pRej = 0;
          } else { this._pRej = (this._pRej||0)+1; }
        }
      }
      this.pitchHist = this.pitchHist.filter(h=>now-h.t < Math.max(this.TREM_WIN_MS, this.TREM_SLOW_WIN_MS));
      // 세기 떨림용 기록 — 1 에서 잘리는 level 이 아니라 원래 rms 의 dB 를 쓴다.
      // 발성 중에만, 그리고 소리 시작 직후 상승 구간(AMP_TREM_SKIP_MS)은 빼고 쌓는다.
      if(level > this.state.thresh){
        if(!this._ampT0) this._ampT0 = now;
        if(now - this._ampT0 > this.AMP_TREM_SKIP_MS){
          const lin = this.demo ? level : (this.rawRms || 0);
          this.ampHist.push({t:now, db:20*Math.log10(Math.max(lin, 1e-7))});
        }
      } else this._ampT0 = 0;
      this.ampHist = this.ampHist.filter(h=>now-h.t < this.TREM_WIN_MS);
      // 잔떨림 = 음높이·세기 잔떨림 중 큰 쪽, 억양 흔들림은 음높이로만. 떨림 = 둘 중 큰 쪽
      const ts = this.computeSlowTremor();
      const tfP = this.computeTremor(now, ts.v > 0 ? ts : null), tfA = this.computeAmpTremor();
      const tf = tfP.v >= tfA.v ? tfP : tfA;
      trem = Math.max(tf.v, ts.v);
      this.tremF += (tf.v - this.tremF)*0.15; if(tf.v > 0) this.tremFHz += (tf.hz - this.tremFHz)*0.1;
      this.tremS += (ts.v - this.tremS)*0.15; if(ts.v > 0) this.tremSHz += (ts.hz - this.tremSHz)*0.1;
      // 움직임(버블 너울)에 쓸 실시간 떨림 — 분절 갭과 무관하게 매 프레임 추종
      this.smoothTrem = (this.smoothTrem||0) + (trem - (this.smoothTrem||0))*0.15;
      this.wave.push({t:now, lvl:this.smoothLvl, p:pitch, v:voiced});
      this.wave = this.wave.filter(w=>now-w.t<3200);

      if(voiced){
        this.lastVoiceT = now;
        if(!this.cur){
          this.cur = { t0:now, segs:[this.mkSeg(vowel, now)], avgPitch:pitch>0?pitch:this.state.basePitch, trem, everRecognized:!!vowel };
        }
        const c = this.cur, last = c.segs[c.segs.length-1];
        last.peak = Math.max(last.peak||0, this.smoothSize);
        // 갭은 한 번 성립하면 걸어둔다(latch) — 세기가 먼저 돌아오고 모음이 100~200ms 늦게 붙어도 분절 유지
        const gapped = (c.gapMs||0) >= this.DIP_MS || !!c.gapLatch;

        // 인식불가 누적은 세그먼트가 아니라 버블(c) 단위로 — 세그에 두면 분절 때마다 0으로 리셋돼 영영 안 터짐
        if(vowel) c.noRecMs = 0;
        else if(c.everRecognized) c.noRecMs = (c.noRecMs||0) + dt;

        // ── 분절 판정 ──
        //  ① 재타격: 세기가 세그 피크의 RELEASE_RATIO 아래로 DIP_MS 이상 꺼졌다 돌아옴 → 같은 모음도 새 덩이
        //  ② 모음 전환: PEND_N 프레임 연속 다른 모음이어야 인정 (한 프레임 튐 무시)
        let split = null;
        if(gapped){
          c.gapLatch = true;
          split = vowel;   // 인식 안 되는 동안은 새 덩이를 만들지 않음 (모음 붙는 프레임에 나눔)
        } else if(vowel && last.v && vowel !== last.v){
          if(vowel === c.pendV) c.pendN = (c.pendN||0)+1; else { c.pendV = vowel; c.pendN = 1; }
          if(c.pendN >= this.PEND_N) split = vowel;
        }

        if(split){
          last.tEnd = now;
          c.segs.push(this.mkSeg(split, now, last));
          c.gapMs = 0; c.gapLatch = false; c.pendV = null; c.pendN = 0;
        } else if(vowel && !last.v && !c.everRecognized){
          last.v = vowel; c.everRecognized = true; c.pendV = null; c.pendN = 0;
        }

        if(c.everRecognized && (c.noRecMs||0) > this.UNREC_MS){
          // 발성 중 인식불가 지속 → 글자가 무너지고 비눗방울이 터짐, 잔해가 화면에 떠다님
          const gy2 = H*this.genRatio(), bx = this.centeredWandAnchor(W,now), by = gy2+(H-gy2)*0.30;
          if(this.gl3dOn()) this.gl3dPopOwner(this.cur); else
          for(let i=0;i<12;i++) this.parts.push({x:bx+(Math.random()-.5)*50, y:by+(Math.random()-.5)*40, vx:(Math.random()-.5)*3, vy:(Math.random()-.5)*3, r:2+Math.random()*5, a:1, a0:Math.random()*6, c: Math.random()<.5?'rgba(18,165,143,.72)':'rgba(255,111,156,.75)'});
          c.segs.filter(s=>s.v).forEach(s=>{ this.ghosts.push({v:s.v, x:bx+(Math.random()-.5)*40, y:by, a:.8, size:20, fall:true}); });
          const nRem = 4+Math.floor(Math.random()*4);
          for(let i=0;i<nRem;i++) this.remnants.push({x:bx+(Math.random()-.5)*70, y:by-10-Math.random()*40, r:4+Math.random()*8, vx:(Math.random()-.5)*.9, vy:-(.4+Math.random()*.6), phase:Math.random()*7, born:now, life:14000+Math.random()*10000});
          this.cur = null;
        }

        if(!this.cur) { /* 터진 직후 프레임 스킵 */ } else {
        const s = c.segs[c.segs.length-1];
        s.peak = Math.max(s.peak||0, this.smoothSize);
        // 세기 → 크기: 비대칭 추종(피크 홀드). 커질 때만 따라가고 줄 땐 버텨, 세그 최대 세기가 크기로 남음
        s.lvl += (this.smoothSize - s.lvl) * (this.smoothSize > s.lvl ? this.LVL_ATTACK : this.LVL_RELEASE);
        // 발성 중 깊은 골도 갭으로 친다 — 재타격 분절의 방아쇠
        if(this.smoothSize < s.peak*this.RELEASE_RATIO){
          c.gapMs = (c.gapMs||0) + dt;
        } else {
          if(!split && !c.gapLatch) c.gapMs = 0;   // 정상 세기 = 갭 리셋 (걸어둔 갭은 유지)
          if(pitch>0){ s.pitch += (pitch - s.pitch)*0.15; c.avgPitch += (pitch-c.avgPitch)*0.05; }
          c.trem += (trem-c.trem)*0.1;
          c.tremF = this.tremF; c.tremFHz = this.tremFHz; c.tremS = this.tremS; c.tremSHz = this.tremSHz;
        }
        s.dur = now - s.t0;
        }
      } else if(this.cur){
        this.cur.gapMs = (this.cur.gapMs||0) + dt;   // 무음 갭도 누적 → 다음 발성이 새 덩이로 붙음
        if(now - this.lastVoiceT > this.state.endHold) this.finishBubble(now, W, H);
      }
      // 안전망: 형성이 MAX_FORM_MS 넘게 이어지면 강제 확정
      if(this.cur && now - this.cur.t0 > this.MAX_FORM_MS) this.finishBubble(now, W, H);
      if(now - this.lastMeterT > 120){
        this.lastMeterT = now;
        this.setState({ level:this.smoothLvl, pitch:pitch>0?Math.round(pitch):0, vowel:vowel||'', voiced,
          dur:this.cur?(now-this.cur.t0)/1000:0, trem });
      }
    }

    this.stepBg(now, pitch);   // 배경 색조 — 그리는 값만 만든다 (절대규칙 2)
    this.drawScene(ctx, W, H, now);
    this.drawGraph(now);
    this.drawPitchGraph(now);
    if(this.DEBUG_TREM){
      ctx.save(); ctx.setTransform(devicePixelRatio,0,0,devicePixelRatio,0,0);
      ctx.fillStyle='rgba(210,20,90,.95)'; ctx.font='13px monospace';
      ctx.fillText('DBG trem='+(trem||0).toFixed(2)+' sm='+(this.smoothTrem||0).toFixed(2)+' ct='+(this.cur?(this.cur.trem||0).toFixed(2):'-')+' | '+(this._td||'-')+' | '+(this._tda||'-')+' | '+(this._tds||'-'), 40, 150);
      ctx.restore();
    }
  };

  // 부착 각도 = 피치 변화가 결정 + 소량 지터(±15°)
  // 기준 진행 방향은 오른쪽(0°): 다음 모음 피치가 직전보다 높으면 위로, 낮으면 아래로 꺾임
  mkSeg(v, now, prevSeg){
    let ang;
    if(!prevSeg){ ang = Math.random()*Math.PI*2; } // 시작 방향은 버블마다 랜덤 (이후 꺾임은 피치가 결정)
    else {
      const dp = (this.state.pitch||this.state.basePitch) - prevSeg.pitch;
      const bend = Math.max(-1, Math.min(1, dp/80)) * (Math.PI/1.8); // ±100°까지 피치가 결정
      const jitter = (Math.random()-.5) * (Math.PI/6);             // ±15° 지터
      ang = (prevSeg.ang ?? 0) + bend + jitter;
    }
    return { v, t0:now, tEnd:0, lvl:this.smoothSize, pitch:this.state.pitch||this.state.basePitch, dur:0, noRec:0, ang, olap: .62+Math.random()*.16,
      sfx: Math.random()<.5?'trem':'bulge', ifx: 'swirl', seed: Math.random()*7 };   // 인식불가 = 회오리만 (기포는 물방울처럼 보여 제외)
  }

  // 발성 길이 → 막의 불투명도. 0.08 에서 시작해 OPACITY_FULL_S 초에 불투명해진다.
  // 패널의 '길이' 막대가 4초에 꽉 차므로 같은 기준으로 맞췄다 (2.2초 → 4초).
  OPACITY_START = 0.08; OPACITY_FULL_S = 4;
  segAlpha(sec){ return Math.min(1, this.OPACITY_START + sec*(1 - this.OPACITY_START)/this.OPACITY_FULL_S); }
  segStyle(s){
    return { v:s.v, r: this.segRadius(s.lvl), ar: this.aspect(s.pitch),
      alpha: this.segAlpha((s.tEnd-s.t0)/1000), ang: s.ang, olap: s.olap,
      sfx: s.sfx, ifx: s.ifx, seed: s.seed, tone: this.segTone(s.pitch), spin: this.pitchSpin(s.pitch) };
  }
  // ── 버블9 규칙: 발화 당시의 색이 테두리에 남는다 ──────────────────
  // 배경은 지금 내는 음을 따라 계속 흐르지만, 세그먼트는 태어난 순간의 음정을
  // 자기 테두리에 붙들어 둔다. 떠오른 방울은 그때의 색을 그대로 지니고 다닌다.
  // 음정이 없으면(무음·인식불가) 색도 없다 — 회전의 '정지 = 음정 없음'과 같은 규칙.
  segTone(p){ return (p > 0) ? this.pitchTone(p) : null; }
  // 음정은 형태도 색도 아닌 '글자의 회전 속도'로 말한다. 높으면 빨리, 낮으면 천천히.
  aspect(p){ return 1; }
  // ── 버블11: 음정 매핑을 '반음(로그)' + '기준음 자동 추종'으로 바꾼다 ──
  //
  // 버블10 까지는 기준음 대비 '절대 Hz 차 / 150Hz' 였다. 이 자에는 두 가지 문제가 있었다.
  //   1) Hz 차는 음정이 아니다. 사람은 주파수 비(比)로 높낮이를 듣는다.
  //   2) 기준음이 190Hz 로 고정이라, 110~160Hz 로 말하는 남성 목소리는
  //      tone 이 -0.53 ~ -0.20 안에서만 움직였다 — 파장으로는 465~512nm,
  //      즉 파랑에서 청록까지가 전부였다. 빨강에 닿으려면 340Hz 를 내야 했다.
  //      "색이 안 변한다"는 관찰은 이 자의 문제였지 렌더러의 문제가 아니었다.
  //
  // 그래서 ① 반음 단위로 재고(음악적으로 옳다), ② 기준음을 화자의 실제 음역
  // 중심으로 천천히 옮긴다. 누가 말하든 자기 평소 목소리가 스펙트럼 한가운데(연두)에
  // 놓이고, 거기서 올리면 주황·빨강으로, 내리면 청록·파랑·보라로 끝까지 간다.
  PITCH_SPAN = 3.0;      // 반음. 기준에서 ±3.0반음이면 가시광선 양 끝  ※ 4.5 → 3.0: 낮은 소리가 중간색에서 못 벗어나던 문제로 민감도 상향
  BASE_ADAPT = 0.12;     // 기준음이 화자를 따라가는 속도(1/초) — 발성 중에만, 아주 느리게
  PITCH_HZ = 150;        // (구 매핑 잔재 — 더는 쓰지 않는다)
  pitchCenter(){ return this.pitchAvg > 0 ? this.pitchAvg : (this.state.basePitch || 190); }
  pitchTone(p){
    const base = this.pitchCenter();
    if(!(p > 0) || !(base > 0)) return 0;
    return Math.max(-1, Math.min(1, 12*Math.log2(p/base)/this.PITCH_SPAN));
  }
  // ── 버블6 규칙: 음정 → 글자의 '입체' 회전 속도 ──
  // 기준음에서 -1(저음) … 0(기준) … +1(고음) 을 회전 속도로 옮긴다.
  // 저음도 '멈춤'이 아니라 느리게 돌아야 음정이 없는 상태(인식불가)와 구별된다.
  SPIN_MIN = 0.10;                      // 최저음 회전 (바퀴/초)
  SPIN_MAX = 1.05;                      // 최고음 회전 (바퀴/초)
  pitchSpin(p){
    if(!(p > 0)) return 0;              // 음정 없음 = 회전 없음 (의미의 부재)
    const t = (this.pitchTone(p) + 1)/2; // 0..1
    return (this.SPIN_MIN + (this.SPIN_MAX - this.SPIN_MIN)*t) * Math.PI*2 / 1000;
  }
  // 글자 회전 각도. 방울마다 seed 로 시작 위상을 달리해 서로 동기화되지 않게 한다.
  // 부유 중인 방울은 각속도가 계속 줄어들므로 now×spin 으로 계산할 수 없다
  // (배율을 곱하면 각도가 되돌아간다). 그래서 떠오른 뒤에는 프레임마다 적분한
  // 누적각 s.acc 를 쓴다. 생성 중인 방울은 감속이 없으므로 기존 식 그대로.
  spinAngle(s, now){
    if(!s) return 0;
    if(s.acc !== undefined) return s.acc;
    if(!s.spin) return 0;
    return now*s.spin + (s.seed||0)*1.7;
  }

  // 글자는 평면으로 도는 게 아니라 '깊이를 통과하며' 돈다.
  // 정면 → 옆면(획이 한 줄로 섬) → 뒷면(좌우 반전) → 다시 정면.
  // 캔버스 2D 에는 실제 3D 가 없으므로 가로 축소(cos)로 단축법을,
  // 앞뒤 위치(sin)에 따른 크기 변화로 원근을 흉내낸다.
  SPIN_AXIS  = 'y';                     // 'y' = 회전문처럼 좌우로 / 'x' = 카드 뒤집듯 위아래로
  SPIN_PERSP = 0.16;                    // 원근 강도 — 가까울 때 커 보이는 정도 (0 이면 원근 없음)
  applySpin3D(ctx, x, y, s, now){
    const a = this.spinAngle(s, now);
    const c = Math.cos(a);              // 단축법: ±1 정면·뒷면, 0 이면 옆면
    const p = 1 + this.SPIN_PERSP*Math.sin(a);  // 근·원 스케일
    ctx.translate(x, y);
    if(this.SPIN_AXIS === 'x') ctx.transform(p, 0, 0, c*p, 0, 0);
    else                       ctx.transform(c*p, 0, 0, p, 0, 0);
    // 옆면에 가까울수록 살짝 어두워져 두께가 있는 것처럼 읽힌다
    return 0.62 + 0.38*Math.abs(c);
  }
  pitchSemitones(p){
    const base = this.pitchCenter();
    return (p > 0 && base > 0) ? 12*Math.log2(p/base) : 0;
  }

  // 가시광선 스펙트럼. 소리의 주파수를 빛의 주파수로 그대로 옮긴다:
  // 낮은 음 → 400 nm(보라) … 기준 → 540 nm(연두) … 높은 음 → 680 nm(빨강)
  waveRGB(nm){
    let r = 0, g = 0, b = 0;
    if(nm < 440){ r = -(nm - 440)/60; b = 1; }
    else if(nm < 490){ g = (nm - 440)/50; b = 1; }
    else if(nm < 510){ g = 1; b = -(nm - 510)/20; }
    else if(nm < 580){ r = (nm - 510)/70; g = 1; }
    else if(nm < 645){ r = 1; g = -(nm - 645)/65; }
    else { r = 1; }
    return [r, g, b];
  }
  // ── 버블11 규칙: 색은 가시광선 스펙트럼 위에서 움직인다 ──────────────
  //
  // 버블10 은 '한 색상 계열'을 청록–민트–연둣빛 램프로 읽었다. 그 결과 음이
  // 아무리 오르내려도 색이 전부 초록 안에 갇혔고, 화면에서는 아무것도
  // 변하지 않는 것처럼 보였다. 요구는 계열을 초록으로 못박으라는 것이 아니라
  // '한 순간에 한 색만 보이게 하라'(= 무지개 띠 금지)는 것이었다.
  //
  // 그래서 자는 다시 파장으로 되돌린다. 소리의 주파수를 빛의 주파수로 옮긴다:
  //   낮은 음 → 400nm(보라·파랑) … 기준음 → 540nm(연두) … 높은 음 → 680nm(빨강)
  // '한 계열'은 대신 공간에서 지킨다 — 화면 어느 자리에서나 파장은 하나이고,
  // 바깥으로 갈수록 옅어지기만 한다(spread 를 거의 0 으로 둔다).
  SPEC_LO = 400;   // nm — 음역 아래끝
  SPEC_HI = 680;   // nm — 음역 위끝
  famRGB(t){
    const k = Math.max(-1, Math.min(1, t || 0));
    const nm = this.SPEC_LO + (k + 1)/2*(this.SPEC_HI - this.SPEC_LO);
    const c = this.waveRGB(nm);
    return [c[0]*255, c[1]*255, c[2]*255];
  }
  // 흰빛 쪽으로 들어올려 농도를 낮춘다 (P 가 클수록 옅다)
  famPale(t, P){
    const c = this.famRGB(t);
    return [c[0] + (255-c[0])*P, c[1] + (255-c[1])*P, c[2] + (255-c[2])*P];
  }
  toneRGB(t){ return this.famPale(t, 0.62); }
  // 테두리에 남는 색. 띠가 얇으므로 막 전체를 물들일 때보다 덜 흐리게 만든다
  // (P 를 올리면 흰빛에 묻혀 색이 안 읽히고, 0 에 가까우면 스티커처럼 뜬다).
  RIM_P    = 0.20;   // 흰빛으로 들어올리는 정도 (순수 스펙트럼색은 채도가 너무 높다)
  RIM_GAIN = 1.05;   // 테두리 색의 전체 진하기
  rimRGB(t){ return this.famPale(t, this.RIM_P); }

  // ── 버블7 규칙: 음정 → 배경 공기의 색 ──────────────────────────────
  // 방울은 여전히 무채색이다(절대규칙 3). 색은 막이 아니라 '공기'가 말한다.
  // 지금 내는 음이 낮으면 보라·파랑 쪽, 기준음이면 연두, 높으면 주황·빨강 쪽으로
  // 배경이 물든다 — 자는 방울과 똑같이 pitchTone() 이다.
  // 음정이 없으면(무음·인식불가) 색이 빠져 원래의 유리온실 민트로 돌아간다.
  // 회전에서 '정지 = 음정 없음'이었던 것과 같은 규칙을 색에서도 지킨다.
  BG_HUE_RATE = 3.2;    // 색조가 새 음정을 따라가는 속도 (1/초) — 음이 튀어도 색은 천천히
  BG_RISE     = 2.4;    // 발성 시작 → 색이 배는 속도 (1/초)  ※ 3.0 → 1.2: 너무 민감하게 뿌예져서 낮춤
  BG_FALL     = 0.5;    // 발성이 끊긴 뒤 색이 빠지는 속도 — 느리게 두어 여운을 남긴다
  // gain = 최대 농도, pale = 흰빛으로 들어올리는 정도(클수록 옅음), air = 전역 틴트 비율,
  // spread = 블룸 가장자리로 벌어지는 파장 폭(무지개 띠의 넓이)
  // ※ 버블9 에서 농도를 낮췄다(의뢰인 요청: 배경이 주인공이 되어 방울이 안 보였다).
  //   색을 말하는 자리가 배경 하나에서 '배경 + 방울 테두리' 둘로 늘었으므로,
  //   배경은 공기로 물러나고 테두리가 개별 방울의 음정을 맡는다.
  //   spread(무지개가 벌어지는 폭)는 그대로다 — 여기를 줄이면 단색 틴트가 된다.
  // veil = 색을 얹기 전에 까는 흰 막. 페이지 바탕이 민트라 그 위에 옅은 색을
  //   칠하면 파랑이 청록으로, 빨강이 탁한 살구색으로 먹힌다. 한 번 비우고
  //   칠해야 낮은 농도에서도 색상(hue)이 제 색으로 읽힌다.
  // spread 는 거의 0 이다 — 화면 어디서나 파장은 하나(무지개 띠 금지).
  BG_SOFT  = { gain:0.27, pale:0.26, air:0.09, spread:0.06, veil:0.06 };  // 은은(기본값)  ※ gain·air·veil 낮춤 — 발성 때 화면이 뿌예지는 걸 줄임
  BG_VIVID = { gain:0.46, pale:0.16, air:0.14, spread:0.10, veil:0.11 };   // 뚜렷
  BG_GRAY = true;

bgRGB(t, P){
  if(!this.BG_GRAY){
    return this.famPale(t,P);
  }

  // 음정을 색상이 아니라 밝기로 표현
  // 낮은 음  → 어두움
  // 기준음   → 중간 밝기
  // 높은 음  → 밝음
  const L = 0.28 + 0.62*((t+1)/2);
  const g = Math.round(
    255*Math.min(1,L + P*0.15)
  );

  return [g,g,g];
}
  // ── 배경과 발화색의 대비 ──────────────────────────────────────────
  // 배경이 발화색과 똑같으면 지금 만들어지는 방울이 배경에 그대로 묻힌다.
  //
  // 처음엔 파장을 일정 간격 벌리는 방식을 썼는데, 스펙트럼은 고리가 아니라
  // 선분이라 실패했다. 400nm(보라)와 680nm(빨강)는 색상환에서 이웃이 아니므로
  // 고음에서 간격이 끝에 닿는 순간 배경이 빨강→보라로 순간이동한다.
  // 잘라 내면 이번엔 고음에서 간격이 0이 되어 애초의 문제로 돌아간다.
  //
  // 그래서 파장이 아니라 '농도'로 벌린다. 배경과 방울은 언제나 같은 파장을
  // 쓰되(= 톤이 어긋날 수 없다), 배경만 흰빛 쪽으로 더 들어올려 옅게 만든다.
  // 어느 음정에서도 간격이 일정하고, 색이 튀는 지점이 없다.
  //   bgShift 0 → 배경과 방울이 같은 색   1 → 배경이 거의 흰빛에 가까운 색조
  bgPaleAdd(){ return (this.state.bgShift ?? 0) * 0.22; }
  // 배경 위에 덮이는 층들이 원근선 대비를 얼마나 깎는지 추정해, 그 역수만큼 선을 키운다.
  // 상수를 하드코딩하지 않고 실제로 칠하는 값(veil·gain·air·bgDepth 광량)에 묶는다.
  bgLineBoost(){
    const M = this.state.bgMode === 'vivid' ? this.BG_VIVID
            : this.state.bgMode === 'soft'  ? this.BG_SOFT : null;
    const bd = this.state.bgDepth || 0;
    let keep = 1;
    if(M){
      const pAdd = this.bgPaleAdd();
      const A = this.bgWeight * M.gain * (1 - pAdd*0.55) * (1 + 0.35*Math.min(1, this.smoothLvl*2.2));
      keep *= (1 - this.bgWeight*M.veil);   // 흰 막
      keep *= (1 - A*0.6);                  // 음정 블룸(화면 평균)
      keep *= (1 - A*M.air);                // 전역 틴트
    }
    keep *= (1 - bd*0.6*0.55*0.4);          // 배경 진하기의 위쪽 흰 광량(평균)
    const k = (1/Math.max(0.25, keep)) * (1 + 0.45*bd);   // 진해질수록 절대 명도가 내려가므로 조금 더
    return Math.min(3, k);
  }
  stepBg(now, pitch){
    const dt = Math.min(64, now - (this.bgT || now)); this.bgT = now;
    const k = dt/1000;
    const on = pitch > 0 && this.smoothLvl > this.state.thresh;
    if(on) this.bgTone += (this.pitchTone(pitch) - this.bgTone)*Math.min(1, k*this.BG_HUE_RATE);
    const rate = on ? this.BG_RISE : this.BG_FALL;
    this.bgWeight += ((on ? 1 : 0) - this.bgWeight)*Math.min(1, k*rate);
  }
  // 색은 목소리가 들어오는 자리(생성 공간의 앵커)에서 피어올라 공기로 번진다.
  // 화면을 균일하게 덮으면 색이 '조명'이 아니라 '색지'로 읽힌다.
  //
  // 블룸은 한 가지 색이 아니라 '무지개 무리'다 — 중심은 지금 내는 음의 파장이고,
  // 바깥으로 갈수록 파장이 spread 만큼 벌어져 이웃한 스펙트럼색이 띠로 드러난다.
  // 프리즘을 통과한 빛이 한 점이 아니라 띠로 퍼지는 것과 같은 구조다.
  // 그래서 음이 움직이면 무지개 전체가 스펙트럼을 따라 흐른다.
  drawBgWash(ctx, W, H, now){
    const M = this.state.bgMode === 'vivid' ? this.BG_VIVID
            : this.state.bgMode === 'soft'  ? this.BG_SOFT : null;
    return; // 배경은 항상 순수 검정 — 발성에 따른 색 번짐 없음
    if(!M || this.bgWeight < 0.004) return;
    const gy = H*this.genRatio();
    const ax = W/2, ay = gy + (H-gy)*0.45;
    // 아주 느린 숨 + 지금 내는 소리의 세기. 색이 '발화에 맞춰' 밀도까지 움직인다.
    const pAdd = this.bgPaleAdd();
    const A = this.bgWeight * M.gain * (1 - pAdd*0.55) * (1 + 0.06*Math.sin(now/2200))
                                     * (1 + 0.35*Math.min(1, this.smoothLvl*2.2));   // 세기 연동 0.55 → 0.20
    const t0 = this.bgTone;
    // 파장이 벌어지는 방향도 아주 천천히 흔들려 띠가 굳어 보이지 않게 한다
    const sw = M.spread * (1 + 0.10*Math.sin(now/3100));
    // 파장이 가시광선 밖으로 나가면 잘라 버리는 대신 접어서 되돌린다.
    // 잘라 두면 고음·저음에서 띠가 한 색으로 뭉개져 무지개가 사라진다.
    // 한 계열 안에서만 움직이므로 파장을 접을 필요가 없다 — 끝에서 잘라 둔다.
    const clamp = t => t < -1 ? -1 : (t > 1 ? 1 : t);
    const stop = (dt, k)=>{
      const c = this.bgRGB(clamp(t0 + dt), Math.min(0.94, M.pale + pAdd));
      return 'rgba('+Math.round(c[0])+','+Math.round(c[1])+','+Math.round(c[2])+','+(A*k).toFixed(4)+')';
    };
    ctx.save();
    // 0. 흰 막으로 바탕의 민트를 걷어낸다 — 그 위에 칠해야 파랑이 파랑으로 읽힌다
    ctx.fillStyle =
  'rgba(255,255,255,'+
  (this.bgWeight*M.veil*0.5).toFixed(4)+
  ')';
    ctx.fillRect(0, 0, W, H);
    const g = ctx.createRadialGradient(ax, ay, 0, ax, ay, Math.hypot(W, H)*0.82);
    g.addColorStop(0,   stop(0,        1.00));  // 중심 = 지금 이 음의 파장
    g.addColorStop(.20, stop(sw*0.35,  0.82));
    g.addColorStop(.42, stop(sw*0.75,  0.56));  // 바깥으로 갈수록 파장이 벌어진다
    g.addColorStop(.68, stop(sw*1.15,  0.28));
    g.addColorStop(1,   stop(sw*1.60,  0));
    ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
    // 공기 전체에 배는 틴트 — 반대쪽으로 조금 벌려 화면 위아래가 다른 파장을 띤다
    const gv = ctx.createLinearGradient(0, 0, 0, H);
    gv.addColorStop(0, stop(-sw*0.60, M.air));
    gv.addColorStop(1, stop( sw*0.25, M.air*0.7));
    ctx.fillStyle = gv; ctx.fillRect(0, 0, W, H);
    ctx.restore();
  }

  finishBubble(now, W, H){
    const c = this.cur; this.cur = null;
    c.segs[c.segs.length-1].tEnd = now;
    c.segs = c.segs.filter(s=>(s.tEnd-s.t0)>140);
    if(!c.segs.length) return;
    const gy = H*this.genRatio();
    const b = {
      segs: c.segs.map(s=>this.segStyle(s)),
      x: W/2, y: 0, vy:-3.4,
      avgPitch: c.avgPitch, endPitch: c.segs[c.segs.length-1].pitch, born: now, life: 8000+Math.random()*6000,
      trem: Math.min(1, this.smoothTrem || c.trem), merges: 0,
      tremF: c.tremF||0, tremFHz: c.tremFHz||6, tremS: c.tremS||0, tremSHz: c.tremSHz||1, _phS: c._phS||0, _phF: c._phF||0, durSec: (now-c.t0)/1000,
      death: 'spindown', // 회전이 멎으면 터진다
      phase: Math.random()*Math.PI*2, rot:(Math.random()-.5)*.3, dead:false, rising:true
    };
    // ── 버블10 규칙: 부유 후 회전은 점차 느려지고, 멎는 순간 터진다 ──────
    // 발화가 길수록 오래 돈다(= 오래 산다). 각속도는 세그먼트의 음정 회전을
    // 이어받고, spinK 가 1 → 0 으로 줄면서 그 값을 깎는다.
    // 누적각의 출발점은 '생성 중에 보이던 그 각도' 그대로여야 한다.
    // 0 에서 시작하면 떠오르는 순간 글자가 딴 각도로 순간이동한다.
    b.segs.forEach((s,i)=>{ const src = c.segs[i]; s.acc = (src && src.fAcc !== undefined) ? src.fAcc : (s.seed||0)*1.7; });
    // 떠오르기 시작하는 자리 = 고리에 걸려 있던 바로 그 자리 (순간이동 금지)
    const age=now-c.t0,t=age/470,p=1-Math.exp(-t)*(1+t);
    this.wandCenterOffset=this.soapPort(b).x+8+76*p;
    const pose=this.soapPose(b,Math.min(W-40, this.wandBaseX(W)+this.wandCenterOffset),gy+(H-gy)*.30,age);
    b.x=pose.x; b.y=pose.y;
    // 부유는 떠오르기 시작한 이 순간부터다 — 감속도 여기서 시작한다.
    b.spinK = 1; b.floatT = now;
    b.life = Math.min(20000, 6500 + b.durSec*1900 + Math.random()*3200);
    // 첫 벽 충돌 높이 = 음높이: 높으면 위쪽, 낮으면 아래쪽(경계선 근처)
    const pt = Math.max(0, Math.min(1, (b.avgPitch - this.state.basePitch + 150)/300));
    b.riseTo = (gy-80)*(1-pt) + H*0.08*pt + (Math.random()-.5)*30;
    b.wallDir = Math.random() < 0.5 ? -1 : 1; // 좌우 랜덤 — 항상 오른쪽으로만 쏠리던 것 수정
    b.vx = b.wallDir*(0.9+Math.random()*0.9); // 생성 각도 그대로 기울어 올라가며 바로 사이드로
    b.drift = Math.max(-.35, Math.min(.35, (b.avgPitch-this.state.basePitch)/150*.35));
    this.anchorBorn = now; // 기본 원형 버블이 중앙 하단에 새로 등장
    this.bubbles.push(b);
    if(this.bubbles.length>24){ const old=this.bubbles.shift(); }
  }

  // ── 버블10 규칙: 붙는 모양은 전체적으로 '둥글게' ────────────────────
  // 사슬로만 이으면 모음이 늘수록 지렁이처럼 길쭉해진다. 실제 비눗방울 무리는
  // 표면장력 때문에 덩어리째 둥글게 모인다. 그래서 두 단계로 배치한다.
  //   1) 사슬: 피치가 정한 방향(ang)으로 이어 붙인다 — 순서·의미는 그대로 보존
  //   2) 이완: 중심으로 당기면서 겹침만 밀어낸다 — 실루엣이 원에 수렴한다
  // 결정론적(난수 없음)이라 같은 방울은 매 프레임 같은 배치가 나온다.
  ROUND_PULL = 0.13;   // 중심으로 당기는 힘 (0 이면 예전의 사슬 배치로 되돌아간다)
  ROUND_ITER = 16;     // 이완 반복 횟수
  layoutSegs(segs){
    const n = segs.length;
    // 떠오른 방울의 segs 는 병합될 때만 바뀐다(길이로 판별). 이완은 비싸므로 캐시.
    // 생성 중인 방울은 매 프레임 새 배열이라 자연히 캐시가 비껴간다.
    if(segs.__lay && segs.__layN === n) return segs.__lay;
    const ps=[{x:0,y:0}];
    for(let i=1;i<n;i++){
      // 글자가 안 겹치도록: 두 글자 크기 합보다는 항상 멀게
      const minD = (segs[i-1].r*.62 + segs[i].r*.62)*.85 + 8;
      const d = Math.max((segs[i-1].r+segs[i].r)*(segs[i].olap ?? .62), minD);
      const a=segs[i].ang ?? 0;
      ps.push({x:ps[i-1].x+Math.cos(a)*d, y:ps[i-1].y+Math.sin(a)*d});
    }
    if(n > 2){
      // 두 방울 사이의 최소 간격 — 붙되(겹치되) 글자는 안 겹치는 거리
      const gap = (i,j)=>{
        const ri = segs[i].r, rj = segs[j].r;
        const ol = ((segs[i].olap ?? .62) + (segs[j].olap ?? .62))*.5;
        return Math.max((ri+rj)*ol, (ri+rj)*.53 + 8);
      };
      for(let it=0; it<this.ROUND_ITER; it++){
        let cx=0, cy=0;
        for(const p of ps){ cx+=p.x; cy+=p.y; }
        cx/=n; cy/=n;
        // (1) 중심 인력 — 사슬을 접어 덩어리로 만든다
        for(const p of ps){ p.x += (cx-p.x)*this.ROUND_PULL; p.y += (cy-p.y)*this.ROUND_PULL; }
        // (2) 겹침 해소 — 접히면서 포개진 방울들을 서로 밀어낸다
        for(let i=0;i<n;i++) for(let j=i+1;j<n;j++){
          let dx = ps[j].x-ps[i].x, dy = ps[j].y-ps[i].y;
          let d = Math.hypot(dx, dy);
          if(d < 1e-3){ // 완전히 포개지면 결정론적 방향으로 살짝 벌린다
            const a = (i*2.3999 + j*1.7);
            dx = Math.cos(a); dy = Math.sin(a); d = 1;
          }
          const md = gap(i,j);
          if(d < md){
            const k = (md-d)/d*0.5;
            ps[i].x -= dx*k; ps[i].y -= dy*k;
            ps[j].x += dx*k; ps[j].y += dy*k;
          }
        }
      }
    }
    let cx=0,cy=0; ps.forEach(p=>{cx+=p.x;cy+=p.y}); cx/=ps.length; cy/=ps.length;
    const out = ps.map(p=>({x:p.x-cx,y:p.y-cy}));
    try { Object.defineProperty(segs,'__lay',{value:out,writable:true,configurable:true});
          Object.defineProperty(segs,'__layN',{value:n,writable:true,configurable:true}); } catch(e){}
    return out;
  }
  bubbleW(b){ // 군집 지름
    const ps=this.layoutSegs(b.segs);
    let R=0; b.segs.forEach((s,i)=>{ R=Math.max(R, Math.hypot(ps[i].x,ps[i].y)+s.r); });
    return R*2;
  }

  // Reflect only the canvas scene. HTML controls and the graph stay unchanged.
  // Counter-reflect glyphs at their own origin so Korean text remains readable.
  rightwardContext(ctx){
    this._rwMap = this._rwMap || new WeakMap();
    if(this._rwMap.has(ctx)) return this._rwMap.get(ctx);
    const cache=new Map();
    const px=new Proxy(ctx,{
      get(target,key){
        if(cache.has(key)) return cache.get(key);
        const value=Reflect.get(target,key,target);
        if(typeof value!=='function') return value;
        let fn;
        if(key==='fillText'||key==='strokeText'){
          fn=(text,x,y,...rest)=>{
            target.save();
            try{
              target.translate(x,y);target.scale(-1,1);
              const align=target.textAlign;
              const rtl=target.direction==='rtl';
              if(align==='left'||(align==='start'&&!rtl)||(align==='end'&&rtl)) target.textAlign='right';
              else if(align==='right'||(align==='end'&&!rtl)||(align==='start'&&rtl)) target.textAlign='left';
              value.call(target,text,0,0,...rest);
            }finally{target.restore();}
          };
        }else fn=value.bind(target);
        cache.set(key,fn);return fn;
      },
      set(target,key,value){return Reflect.set(target,key,value,target);}
    });
    this._rwMap.set(ctx, px);
    return px;
  }
  drawScene(ctx,W,H,now){
    const on = this.gl3dOn();
    if(this.gl3d && this._glVis !== on){
      this._glVis = on;
      this.gl3d.canvas.style.visibility = on ? 'visible' : 'hidden';
      this.bgCanvas.style.visibility = on ? 'visible' : 'hidden';
      this.gl3d.bgCanvas.style.visibility = on ? 'visible' : 'hidden';
    }
    this._glCap = on; this._gl3dOwner = null;
    if(on){
      this._glPrev = this._glFrame || new Map(); this._glFrame = new Map();
      this.gl3d.begin(now);
      this.gl3d.horizon(H/3, W*0.5);   // 소실점: 화면 위쪽 1/3 지점, 가로 가운데
      // 소실점 원근선은 배경 진하기·배경 색 반응과 무관하게 항상 같은 세기로 보여야 한다.
      // 위에 덮이는 층(흰 막·음정 블룸·틴트·광량)이 선의 대비를 깎는 만큼 GL 쪽에서 되살린다.
      this.gl3d.lines(this.bgLineBoost());
      const bg = this.bgCtx;
      bg.setTransform(devicePixelRatio,0,0,devicePixelRatio,0,0); bg.clearRect(0,0,W,H);
      bg.save();
      try{ bg.translate(W,0); bg.scale(-1,1); this.drawBgSource(this.rightwardContext(bg),W,H,now); }
      finally{ bg.restore(); }
    }
    ctx.save();
    try{
      ctx.translate(W,0);ctx.scale(-1,1);
      this.drawSceneSource(this.rightwardContext(ctx),W,H,now);
    }finally{ctx.restore(); this._glCap = false;}
    if(on) this.gl3d.render();
  }
  drawSceneSource(ctx, W, H, now){
    const dt = Math.min(64, now - (this.sceneT || now)); this.sceneT = now;
    const gy = H*this.genRatio();
    if(!this._glCap) this.drawBgSource(ctx, W, H, now);

    const ax = this.centeredWandAnchor(W,now), ay = gy + (H-gy)*0.30;
    // ── 버블14 규칙: 방울은 '막대'에서 나온다 ──────────────────────
    // 아무것도 없는 허공에서 방울이 솟는 게 아니라, 생성 공간 한가운데 꽂힌
    // 막대 끝 고리에 막이 걸려 있고, 목소리가 들어오면 그 막이 부풀어 방울이
    // 된다. 생성 지점은 언제나 이 고리 하나다.
    this.stepWandMotion(ax,ay,H,now,dt);
    this.stepWandHead(now,dt);
    this.drawWand(ctx, ax, ay, H, now);
    if(!this.cur){
      // 고리에 걸린 빈 막 — 새로 걸릴 때 서서히 차오른다
      const k = this.anchorBorn ? Math.min(1,(now-this.anchorBorn)/500) : 1;
      const e = 1-Math.pow(1-k,3);
      this.drawWandFilm(ctx, ax, ay, now, e);
      ctx.save(); ctx.globalAlpha = .5*e; ctx.fillStyle='rgba(46,87,95,.8)';
      ctx.font = '600 12px ' + this.UIFONT; ctx.textAlign='center';
      ctx.fillText('음성 인식 대기', ax-4, ay+34*this.wandHeadScale+27);
      ctx.restore();
    } else {
      this.drawForming(ctx, ax, ay, now);
    }

    for(const b of this.bubbles){
      const age = now-b.born;
      const rad = this.bubbleW(b)/2*.75;
      if(!this.state.freeze){
      // 박수로 예약된 터짐: 상승/부유/바람에 밀린 상태 어디서든 b.popAt 이 되면 터진다.
      // killBubble 이 b.dead 를 세우고, 바로 아래 바람·blown 분기가 모두 !b.dead 로
      // 막혀 있어 같은 프레임에 killBubble 이 두 번 불릴 일은 없다.
      if(b.popAt !== undefined && !b.dead && now >= b.popAt) this.killBubble(b, now);
      // 바람: 막대 고리에서 바깥쪽으로 밀어내 화면 밖으로 흘려보낸다. 한 번 밀린 방울은
      // 벽에 튕기지 않고 그대로 날아간다 — 입김은 지속되는 소리라 밀림도 지속된다.
      const wind = this.state.running ? this.windK : 0;
      if(!b.dead && (wind > 0.05 || b.blown)){
        const dx = b.x - ax, dy = b.y - ay, dl = Math.hypot(dx, dy) || 1;
        const k = wind*0.55*dt/16;
        b.vx += (dx/dl)*k; b.vy += (dy/dl)*k - k*0.25;   // 살짝 위로 띄워 날린다
        if(wind > 0.3) b.blown = true;
      }
      if(b.blown && !b.dead){
        b.rising = false;
        b.vx *= .997; b.vy *= .997;
        const sp = Math.hypot(b.vx, b.vy);
        if(sp < 2.5){ const s = 2.5/(sp || 1); b.vx *= s; b.vy *= s; }   // 바람이 멎어도 멈추지 않는다
        b.x += b.vx; b.y += b.vy;
        // 화면을 벗어나면 사라진다
        if(b.x < -rad*2 || b.x > W+rad*2 || b.y < -rad*2 || b.y > H+rad*2) b.gone = true;
      } else if(b.rising){
        b.y += b.vy; b.x += b.vx; b.vy *= .992;
        // 상승 중에도 좌우 벽에서 튕김
        if(b.x < rad){ b.x = rad; b.vx = Math.abs(b.vx); b.wallDir = 1; }
        if(b.x > W-rad){ b.x = W-rad; b.vx = -Math.abs(b.vx); b.wallDir = -1; }
        // 목표 높이에 닿거나, 부력이 다 떨어졌거나, 너무 오래 오르고 있으면 상승 종료.
        // (높은 음의 목표 높이는 감쇠하는 부력으로 못 닿는 경우가 있다 —
        //  예전에는 수명이 알아서 끝내 줬지만 이제 죽음의 규칙이 '회전 정지'뿐이라
        //  여기서 반드시 부유 상태로 넘겨야 한다.)
        if(b.y < b.riseTo || Math.abs(b.vy) < 0.18 || now - b.born > 5200){
          // 상승 완료 → 음높이에 해당하는 높이에서 벽을 향해 빠르게 흩어짐
          b.rising=false;   // 감속은 태어날 때부터 돌고 있다 — 시계를 되감지 않는다
          b.vx = b.wallDir*(3+Math.random()*1.8); b.vy = (Math.random()-.5)*.5;
          b.tvx = b.vx; b.tvy = b.vy; b.wt = now + 2800;
        }
      } else if(!b.dead){
        if(!b.wt || now > b.wt){
          // 표류 속도는 낮춘다 — 이동은 느리게, 대신 울렁임이 눈에 들어오게
          b.tvx = (Math.random()-.5)*2.4;
          b.tvy = (Math.random()-.5)*1.7 - b.drift*1.2;
          b.wt = now + 1100+Math.random()*1700;
        }
        b.vx += (b.tvx - b.vx)*.035; b.vy += (b.tvy - b.vy)*.035;
        b.x += b.vx; b.y += b.vy;
        // 벽 반사: 반동을 줘서 튕겨나옴 (화면 밖으로 절대 안 나감), 가끔은 부딪히는 순간 바로 터짐
        const bounce = (setX, setY)=>{
          // 벽 충돌 즉사는 없앴다 — 죽음의 규칙은 '회전 정지' 하나로 모은다.
          // (충돌로 인한 대결·터짐은 collide() 에 그대로 남아 있다)
          const k = 1.15 + Math.random()*.35; // 반동 계수
          if(setX!==0){ b.vx = setX*Math.abs(b.vx)*k; b.tvx = setX*Math.abs(b.tvx); }
          if(setY!==0){ b.vy = setY*Math.abs(b.vy)*k; b.tvy = setY*Math.abs(b.tvy); }
          b.wt = now + 900; // 튕긴 방향으로 잠시 유지 후 다시 자유 부유
        };
        if(b.x < rad){ b.x = rad; bounce(1,0); }
        else if(b.x > W-rad){ b.x = W-rad; bounce(-1,0); }
        const top = H*0.04 + rad;
        if(!b.dead && b.y < top){ b.y = top; bounce(0,1); }
        else if(!b.dead && b.y > gy - rad - 6){ b.y = gy - rad - 6; bounce(0,-1); }
      }
      // ── 회전 감속: 부유가 시작된 순간(= 태어난 순간)부터 각속도를 깎는다 ──
      // 상승 중이든 자유 부유 중이든 회전은 한 번도 끊기지 않는다.
      // (버블12 는 이 적분이 !rising 안에 있어서, 상승하는 몇 초 동안 글자가
      //  완전히 멎어 있다가 부유로 넘어가며 다시 도는 것처럼 보였다.)
      if(!b.dead){
        const fa = now - (b.floatT || b.born);
        b.spinK = Math.max(0, 1 - Math.pow(Math.min(1, fa/b.life), 1.22));
        const TAU = Math.PI*2;
        // 다 느려지면 옆면(획이 한 줄로 선 상태)에 멈춰 버리기 쉽다.
        // 마지막 구간에서는 앞으로 가장 가까운 '정면'으로 살짝 당겨,
        // 언제나 정면을 보이며 멎게 한다. 앞으로만 당기므로 역회전은 없다.
        const settle = b.spinK < 0.28 ? Math.pow(1 - b.spinK/0.28, 2) : 0;
        for(const s of b.segs){
          if(s.acc === undefined) continue;
          s.acc += (s.spin||0)*b.spinK*dt;
          if(settle > 0){
            const tgt = Math.ceil(s.acc/TAU)*TAU;
            s.acc += (tgt - s.acc)*Math.min(0.5, settle*dt/700);
          }
        }
        if(b.spinK <= 0.015) this.killBubble(b, now);            // 멎는 순간 터진다
      }
      if(!b.dead && b.rising && now - b.born > 9000) b.rising = false;   // 안전판
      // ── 버블10 규칙: 떨림 → '울렁울렁' 부유 ────────────────────────
      // 지그재그(각진 왕복)는 신경질적으로 읽힌다. 목소리의 떨림은 각이 아니라
      // 너울에 가까우므로, 주기가 서로 다른 느린 사인 두 겹을 x·y 에 어긋나게
      // 실어 8자 궤적에 가까운 너울을 만든다. 진행 방향과 무관한 절대 좌표
      // 오프셋이라 방향이 꺾여도 궤적이 튀지 않는다.
      //   떨림 큼 → 폭이 크고 조금 빠른 울렁임
      //   떨림 작음 → 폭이 좁은 잔잔한 울렁임 (0 이어도 완전히 멎지는 않는다)
      // 기본 너울은 떨림과 무관한 잔잔한 표류만 맡는다. 떨림은 아래 tremWave 가 따로 얹는다.
      const amp = 5, per = 1750;
      const ph  = b.phase;
      const tzx = Math.sin(now/per + ph)*amp*0.62
                + Math.sin(now/(per*1.73) + ph*2.1)*amp*0.26;
      const tzy = Math.sin(now/(per*0.86) + ph*1.6 + 1.57)*amp*0.78
                + Math.cos(now/(per*2.31) + ph)*amp*0.20;
      // 오프셋을 한 번 더 저역통과 — 계수를 낮춰 너울이 더 늘어지게 한다
      b.zx = (b.zx || 0) + (tzx - (b.zx || 0))*0.10;
      b.zy = (b.zy || 0) + (tzy - (b.zy || 0))*0.10;
      }
      // 떨림 흔들림: 진행 방향에 수직으로 (방향 전환이 튀지 않게 수직축도 천천히 따라간다)
      {
        const sp = Math.hypot(b.vx||0, b.vy||0);
        const tnx = sp > .2 ? -(b.vy||0)/sp : 1, tny = sp > .2 ? (b.vx||0)/sp : 0;
        b.tnx = (b.tnx ?? tnx) + (tnx - (b.tnx ?? tnx))*.04;
        b.tny = (b.tny ?? tny) + (tny - (b.tny ?? tny))*.04;
        const nl = Math.hypot(b.tnx, b.tny) || 1;
        const tw = this.tremWave(b, now, b.tnx/nl, b.tny/nl);
        b.twx = tw.x; b.twy = tw.y;
      }
      const zx = (b.zx||0) + (b.twx||0), zy = (b.zy||0) + (b.twy||0);
      ctx.save();
      // 대기 원근: 위쪽(먼 곳)의 방울은 공기에 묻혀 살짝 옅어진다
      ctx.globalAlpha = 0.80 + 0.20*Math.min(1, Math.max(0, b.y/(gy || 1)));
      // 멎기 직전 — 막이 잔떨림을 내며 부푼다. 터짐이 예고된다.
      const brink = (b.spinK < .16) ? (1 - b.spinK/.16) : 0;
      const jx = brink ? Math.sin(now/85 + b.phase*3)*brink*1.1 : 0;
      const jy = brink ? Math.cos(now/77 + b.phase*2)*brink*1.1 : 0;
      ctx.translate(b.x + zx + jx, b.y + zy + jy);
      // 아주 느린 기울임만 — 이건 '회전'이 아니라 떠 있는 것의 흔들림이다
      // 방울 자체는 돌지 않는다 — 떠 있는 것의 느린 기울임뿐이다
      ctx.rotate(Math.sin(now/2600+b.phase)*.06);
      if(brink) ctx.scale(1 + brink*0.045, 1 + brink*0.045);
      const angle=Math.sin(now/2600+b.phase)*.06;
      const dx=ax-b.x-zx-jx,dy=ay-b.y-zy-jy;
      this.drawPeanut(ctx,b,now,age<320?{
        x:dx*Math.cos(angle)+dy*Math.sin(angle),
        y:-dx*Math.sin(angle)+dy*Math.cos(angle),
        ...this.wandFilmAxes(1,1,angle),aperture:29*this.wandHeadScale,rimX:13*this.wandHeadScale,skew:3.5*this.wandHeadScale,progress:age/320
      }:null);
      ctx.restore();
    }
    this.drawWand(ctx,ax,ay,H,now,true);
    this.collide(now);
    this.bubbles = this.bubbles.filter(b=>!b.gone);

    // 잔해 기포: 터진 비눗방울의 작은 기포들이 화면을 둥둥 떠다님
    for(const rm of this.remnants){
      // 잔해 기포도 바람에 함께 날아간다
      const windR = this.state.running ? this.windK : 0;
      if(windR > 0.05 || rm.blown){
        const dx = rm.x - ax, dy = rm.y - ay, dl = Math.hypot(dx, dy) || 1;
        const k = windR*0.8*dt/16;
        rm.vx += (dx/dl)*k; rm.vy += (dy/dl)*k - k*0.25;
        if(windR > 0.3) rm.blown = true;
      }
      if(rm.blown){
        rm.x += rm.vx; rm.y += rm.vy;
        if(Math.hypot(rm.vx, rm.vy) < 2){ rm.vx *= 1.05; rm.vy = rm.vy*1.05 - .05; }
        if(rm.x < -rm.r*2 || rm.x > W+rm.r*2 || rm.y < -rm.r*2 || rm.y > H+rm.r*2){ rm.gone = true; continue; }
        ctx.save(); ctx.globalAlpha = .75; this._gl3dOwner = rm;
        this.drawSoapCircle(ctx, rm.x, rm.y, rm.r, 1, now, .3, rm.phase, null);
        ctx.restore(); continue;
      }
      rm.vx *= .985; rm.vy *= .985;
      rm.x += rm.vx + Math.sin(now/900+rm.phase)*.3;
      rm.y += rm.vy + Math.cos(now/1100+rm.phase)*.2;
      rm.vy *= .996;
      const gyR = H*this.genRatio();
      if(rm.x < rm.r) { rm.x = rm.r; rm.vx = Math.abs(rm.vx); }
      if(rm.x > W-rm.r) { rm.x = W-rm.r; rm.vx = -Math.abs(rm.vx); }
      if(rm.y < H*0.05) { rm.y = H*0.05; rm.vy = Math.abs(rm.vy)*.5; }
      if(rm.y > gyR-rm.r) { rm.y = gyR-rm.r; rm.vy = -Math.abs(rm.vy)*.5; }
      const lifeK = 1 - (now-rm.born)/rm.life;
      if(lifeK <= 0){ rm.gone = true; if(this._glCap){ this.gl3dPopOwner(rm); continue; } this.parts.push({x:rm.x, y:rm.y, vx:0, vy:-.5, r:rm.r*.7, a:.8, a0:0, dot:true, c:'rgba(18,165,143,.55)'}); continue; }
      ctx.save(); ctx.globalAlpha = Math.min(1, lifeK*3)*.75;
      this._gl3dOwner = rm;
      this.drawSoapCircle(ctx, rm.x, rm.y, rm.r, 1, now, .3, rm.phase, null);
      ctx.restore();
    }
    this.remnants = this.remnants.filter(r=>!r.gone);

    for(const g of this.ghosts){
      if(g.fall){ g.y += 1.2; g.vr = (g.vr||0)+.004; g.a -= .012; }
      else { g.y -= .22; g.a -= .005; }
      ctx.globalAlpha = Math.max(0,g.a);
      ctx.fillStyle = 'rgba(18,63,57,.9)'; ctx.font = `700 ${g.size}px ${this.UIFONT}`; ctx.textAlign='center'; ctx.textBaseline='middle';
      ctx.fillText(g.v, g.x, g.y);
    }
    ctx.globalAlpha = 1; ctx.textBaseline='alphabetic';
    this.ghosts = this.ghosts.filter(g=>g.a>0);

    for(const p of this.parts){
      if(p.ring){
        // 터진 자리에 번지는 막의 잔상 — 순수 시각 요소(물리와 상호작용 없음)
        p.r += 3.4; p.a -= .05;
        const al = Math.max(0,p.a);
        ctx.globalAlpha = al*.55;
        ctx.strokeStyle = 'rgba(255,255,255,.9)'; ctx.lineWidth = 1.6;
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r,0,7); ctx.stroke();
        ctx.globalAlpha = al*.3;
        ctx.strokeStyle = 'rgba(18,165,143,.8)'; ctx.lineWidth = .8;
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r*.86,0,7); ctx.stroke();
        continue;
      }
      p.x+=p.vx; p.y+=p.vy; p.vy+=.03; p.a-=.02;
      ctx.globalAlpha = Math.max(0,p.a);
      if(p.dot){
        // 물방울: 하이라이트가 박힌 작은 구슬
        const gd = ctx.createRadialGradient(p.x-p.r*.35, p.y-p.r*.4, p.r*.08, p.x, p.y, p.r);
        gd.addColorStop(0,'rgba(255,255,255,.95)');
        gd.addColorStop(.45, p.c);
        gd.addColorStop(1,'rgba(255,111,156,.5)');
        ctx.fillStyle = gd;
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r,0,7); ctx.fill();
        ctx.strokeStyle = 'rgba(255,255,255,.6)'; ctx.lineWidth = .7;
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r,0,7); ctx.stroke();
      } else {
        // 막 파편: 이리데선트 그라데이션이 흐르는 얇은 리본
        const gs = ctx.createLinearGradient(p.x-p.r, p.y-p.r, p.x+p.r, p.y+p.r);
        gs.addColorStop(0,'rgba(18,165,143,.85)');
        gs.addColorStop(.35,'rgba(255,255,255,.95)');
        gs.addColorStop(.7,'rgba(255,111,156,.85)');
        gs.addColorStop(1,'rgba(150,220,190,.7)');
        ctx.strokeStyle = gs; ctx.lineWidth = 1.8; ctx.lineCap = 'round';
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r,p.a0,p.a0+1.1); ctx.stroke();
        ctx.strokeStyle = 'rgba(255,255,255,.5)'; ctx.lineWidth = .6;
        ctx.beginPath(); ctx.arc(p.x,p.y,p.r*1.06,p.a0+.15,p.a0+.95); ctx.stroke();
        ctx.lineCap = 'butt';
      }
    }
    ctx.globalAlpha=1;
    this.parts = this.parts.filter(p=>p.a>0);
  }

  // ══════════════════════════════════════════════════════════════════
  //  박막 간섭 셸 렌더러 (High-Fidelity)
  //  레퍼런스: 흐린 하늘을 배경으로 역광에서 f/8 · 1/2000s 로 찍은
  //  비눗방울 매크로 사진. 막은 중력으로 아래가 두껍고 정수리는 얇아져
  //  무색으로 검게 비치며, 무지개 띠는 가장자리로 갈수록 촘촘해지고
  //  테두리는 프레넬 반사로 타오른다.
  //
  //  ※ 생성·물리·충돌 알고리즘과는 완전히 분리되어 있다. 여기서 하는
  //    일은 '같은 좌표에 무엇을 칠하는가' 뿐이다.
  // ══════════════════════════════════════════════════════════════════
  UIFONT = 'RoundKR, "SF Pro Rounded", ui-rounded, "Apple SD Gothic Neo", system-ui, sans-serif';
  SHELL_N = 20;     // 막 흐름 애니메이션 프레임 수 (회전 위상이라 완전 순환)
  SHELL_R = 160;    // 베이크 해상도(반지름 px)
  BAKE_MS = 6;      // 프레임당 베이크에 쓸 시간 예산

  // ── 방울 윤곽: 완전한 원이 아니라 '둥글지만 불규칙한' 덩어리 ──────────
  // 실제 비눗방울·물방울 사진에서 정원(正圓)은 드물다. 표면장력이 만든
  // 매끈한 곡률은 그대로 두되, 방울마다 다른 저주파(2·3·5 마디) 요철을
  // 반지름 배율에 실어 형태를 흐트러뜨린다.
  // 건드리는 것은 '그리는 반지름 배율'뿐이다 — s.r · b.x · b.y 는 불변이라
  // 충돌·배치·수명은 원형이던 때와 완전히 같다(절대규칙 1·2).
  BLOB_AMP  = 0.068;      // 반지름 요동 폭 — 실제 비눗방울처럼 눌리고 찌그러진 덩어리
  BLOB_FLOW = 0.000075;   // 형태가 천천히 흐르는 속도 — 빠르면 젤리처럼 출렁여 가짜가 된다
  BLOB_SEG  = 60;         // 윤곽 분할 수 (5 마디까지만 담으므로 이 정도면 각이 안 보인다)

  // 각도 → 반지름 배율. 마디 수가 다른 사인 세 개의 합이라 대역이 좁고,
  // 그래서 아무리 흔들어도 뾰족한 모서리가 생기지 않는다.
  blobK(th, seed, now){
    const t = now*this.BLOB_FLOW;
    const w = Math.sin(2*th + seed*3.7 + t*1.30)*0.52
            + Math.sin(3*th - seed*5.1 - t*0.90)*0.31
            + Math.sin(5*th + seed*8.3 + t*0.55)*0.17;
    return 1 + w*this.BLOB_AMP;
  }
  // 윤곽 패스를 현재 경로에 '추가'한다(beginPath 는 호출자 몫 —
  // drawPeanut 의 evenodd 잘라내기처럼 부분 경로로 쌓아 쓰는 곳이 있다).
  blobPath(ctx, x, y, rx, ry, seed, now, k){
    const N = this.BLOB_SEG, K = (k === undefined ? 1 : k), TAU = 6.283185307;
    for(let i=0;i<N;i++){
      const th = i/N*TAU, g = this.blobK(th, seed, now)*K;
      const px = x + Math.cos(th)*rx*g, py = y + Math.sin(th)*ry*g;
      if(i===0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    }
    ctx.closePath();
  }

  initShell(){
    // 값 노이즈용 해시 테이블 (256×256) — 결정론적이라 매번 같은 막이 나온다
    let s = 1337; const T = new Float32Array(65536);
    for(let i=0;i<65536;i++){ s = (s*1664525 + 1013904223) >>> 0; T[i] = s/4294967296; }
    this.NT = T;
    // 파스텔 셸은 스프라이트를 굽지 않는다(간섭 무늬를 쓰지 않으므로).
    // 베이커 코드는 그대로 두되 완료 표시만 세워 매 프레임 예산을 비운다.
    this.shell = []; this.bakeIdx = 0; this.bk = null; this.shellDone = true;
  }

  nVal(x,y){
    const i = Math.floor(x), j = Math.floor(y), fx = x-i, fy = y-j;
    const u = fx*fx*(3-2*fx), v = fy*fy*(3-2*fy), T = this.NT;
    const i0 = i&255, j0 = (j&255)<<8, i1 = (i+1)&255, j1 = ((j+1)&255)<<8;
    const a = T[j0|i0], b = T[j0|i1], c = T[j1|i0], d = T[j1|i1];
    return a + (b-a)*u + (c-a)*v + (a-b-c+d)*u*v;
  }
  fbm(x,y){
    return this.nVal(x,y)*0.55
         + this.nVal(x*2.13+17.3, y*2.13-9.1)*0.29
         + this.nVal(x*4.37-6.2,  y*4.37+11.7)*0.16;
  }

  newBake(k){
    const R = this.SHELL_R, P = 3, S = (R+P)*2;
    const cvs = document.createElement('canvas'); cvs.width = S; cvs.height = S;
    const c2 = cvs.getContext('2d');
    const img = c2.createImageData(S,S);
    const t = k/this.SHELL_N, rot = t*Math.PI*2;
    return { cvs, c2, img, D: img.data, S, R, C:S/2, y:0,
             cr: Math.cos(rot), sr: Math.sin(rot) };
  }

  // 막 두께(nm). 중력 배수 + 정수리 박막 + 실루엣 근처의 링 압축.
  filmD(v, cosI, swK, D_TOP, D_BOT){
    const gz = (v + 1)*0.5;                            // 0 = 정수리, 1 = 바닥
    let d = D_TOP + (D_BOT - D_TOP)*Math.pow(gz, 1.25);
    d *= swK;
    d *= 0.42 + 0.58*(gz*2.2 < 1 ? gz*2.2 : 1);        // 정수리는 배수가 끝나 얇다
    // 실루엣 근처에서는 한 픽셀이 구면의 넓은 범위를 담아
    // 남은 간섭 띠가 전부 가장자리로 몰린다 — 사진의 동심 링
    d *= Math.pow(1/(cosI < 0.02 ? 0.02 : cosI), 0.20);
    return d < 20 ? 20 : d;
  }

  // 행 단위 재개 가능 베이크. 다 그렸으면 true.
  bakeRows(b, nRows){
    const { D, S, R, C, cr, sr } = b;
    const n = 1.34, F0 = 0.0208;              // 비눗물 굴절률 / 수직입사 반사율
    const LR = 612, LG = 549, LB = 464;       // R·G·B 대표 파장(nm)
    const D_TOP = 210, D_BOT = 980;           // 막 두께 범위(nm) — 중력 배수
    const LX = -0.46, LY = -0.50;             // 광원 방향(좌상단)
    const yEnd = Math.min(S, b.y + nRows);
    for(let py = b.y; py < yEnd; py++){
      const v = (py - C)/R, vv = v*v;
      const rowOff = py*S*4;
      for(let px = 0; px < S; px++){
        const u = (px - C)/R;
        const s2 = u*u + vv;
        if(s2 >= 1) continue;
        const s = Math.sqrt(s2);
        const cosI = Math.sqrt(1 - s2);                 // 입사각
        const sinT = s/n, cosT = Math.sqrt(1 - sinT*sinT); // 굴절각

        // ── 막 두께: 중력 배수 + 회전하는 소용돌이 무늬 ──
        const ax =  u*cr + v*sr, ay = -u*sr + v*cr;      // 정방향 회전
        const bx =  u*cr - v*sr, by =  u*sr + v*cr;      // 역방향 회전
        // 배수 흐름은 가로로 늘어난다 — 노이즈도 같은 비율로 눌러 준다
        const sw = (this.fbm(ax*1.15 + 5.1, ay*1.70 - 3.4) - 0.5)*1.25
                 + (this.fbm(bx*2.40 - 8.7, by*3.50 + 6.3) - 0.5)*0.62
                 + (this.fbm(ax*5.30 + 2.2, ay*7.10 + 9.5) - 0.5)*0.26;
        const swK = 1 + sw*0.52;                         // 띠 구조를 무너뜨리지 않을 만큼만
        const d = this.filmD(v, cosI, swK, D_TOP, D_BOT);

        // ── 박막 간섭: δ = 2π·2nd·cosθt/λ + π ──
        const TP = 6.283185307, dl = 2*n*d*cosT;
        let Ir = 0.5 - 0.5*Math.cos(TP*dl/LR + Math.PI);
        let Ig = 0.5 - 0.5*Math.cos(TP*dl/LG + Math.PI);
        let Ib = 0.5 - 0.5*Math.cos(TP*dl/LB + Math.PI);

        // ── 프린지 안티에일리어싱 ──
        // 가장자리로 갈수록 간섭 띠가 픽셀보다 촘촘해진다. 위상 기울기를
        // 재서 나이퀴스트를 넘는 만큼 대비를 죽이면(= 실제 렌즈가 하는 일)
        // 무아레 대신 사진처럼 중성적인 흰 띠가 남는다.
        const e = 1/R;
        const sa = (u+e)*(u+e) + vv;
        const ca = sa >= 0.9996 ? 0.02 : Math.sqrt(1 - sa);
        const ta = Math.sqrt(1 - sa/(n*n));
        const sb = u*u + (v+e)*(v+e);
        const cb = sb >= 0.9996 ? 0.02 : Math.sqrt(1 - sb);
        const tb = Math.sqrt(1 - sb/(n*n));
        const O  = dl/LG;
        const gu = 2*n*this.filmD(v,   ca, swK, D_TOP, D_BOT)*ta/LG - O;
        const gv = 2*n*this.filmD(v+e, cb, swK, D_TOP, D_BOT)*tb/LG - O;
        const gg = gu*gu + gv*gv;
        if(gg > 0.0004){
          const ct = Math.exp(-6.0*gg);
          Ir = 0.5 + (Ir - 0.5)*ct; Ig = 0.5 + (Ig - 0.5)*ct; Ib = 0.5 + (Ib - 0.5)*ct;
        }

        // ── 3차원 셰이딩: 반사 벡터로 환경을 샘플링 ──
        // N = (u, v, cosI), V = (0,0,1) → Refl = 2(N·V)N − V
        // 하늘을 향한 면은 밝고 지면을 향한 면은 어둡다. 이 한 축이
        // 평면 원반을 '구'로 읽히게 만든다.
        let ry = 2*cosI*v; if(ry < -1) ry = -1; else if(ry > 1) ry = 1;
        const envL = 0.16 + 0.84*(0.5 - 0.5*ry);

        // ── 프레넬: 유리 광택의 본체. 중앙은 거의 투명, 가장자리는 타오른다 ──
        const F = F0 + (1 - F0)*Math.pow(1 - cosI, 3.1);

        // 간섭색은 '줄무늬'가 아니라 흰 광택 위에 배어나는 색조로만 쓴다
        const mx = Ir > Ig ? (Ir > Ib ? Ir : Ib) : (Ig > Ib ? Ig : Ib);
        const mn = Ir < Ig ? (Ir < Ib ? Ir : Ib) : (Ig < Ib ? Ig : Ib);
        const rng = mx - mn;
        let ti = 1, tj = 1, tk = 1;
        if(rng > 0.02){
          const TI = 0.19;                              // 간섭 기여도 (줄무늬 억제)
          ti = 1 - TI*(1 - (Ir - mn)/rng);
          tj = 1 - TI*(1 - (Ig - mn)/rng);
          tk = 1 - TI*(1 - (Ib - mn)/rng);
        }

        let A = (0.010 + F*0.84)*(0.48 + 0.52*envL);

        // ── 하단 크레센트: 아래쪽 가장자리에서 되비치는 밝은 초승달 ──
        const cq = (s - 0.900)/0.055;
        let cw = 0.5 + 0.5*(v*0.84 + u*0.54);
        if(cw < 0) cw = 0;
        const cres = Math.exp(-cq*cq)*cw*cw*cw;
        A += cres*0.44;

        // ── 실루엣: 밝은 백열 링 + 그 안쪽의 가는 굴절 암대 ──
        const rg = (s - 0.9805)/0.0155;
        const rim = Math.exp(-rg*rg);
        const dg = (s - 0.9520)/0.0165;
        const dark = Math.exp(-dg*dg);
        const rimL = rim*(0.55 + 0.45*envL);   // 빛을 받는 쪽 테두리가 더 탄다
        A += rimL*0.82 + dark*0.18;

        // ── 스페큘러: 큰 광택 + 날카로운 글린트 + 뒷면 반사점 ──
        const dx1 = u - LX, dy1 = v - LY, r1 = dx1*dx1 + dy1*dy1;
        const dx2 = u + LX*0.60, dy2 = v + LY*0.60, r2 = dx2*dx2 + dy2*dy2;
        const spec = 1.45*Math.exp(-r1/0.0034) + 0.30*Math.exp(-r1/0.075)
                   + 0.50*Math.exp(-r2/0.0090);
        A += spec*0.95;

        // 밝기: 환경광 + 하이라이트. 색은 흰 광택에 간섭 색조가 밴 것.
        const V0 = 0.60 + 0.40*envL;
        let R8 = ti*V0 + spec + rimL*0.56 + cres*0.42 - dark*0.30;
        let G8 = tj*V0 + spec + rimL*0.59 + cres*0.46 - dark*0.28;
        let B8 = tk*V0 + spec + rimL*0.64 + cres*0.52 - dark*0.23;

        A *= Math.min(1, (1 - s)*R/0.85);   // 안티에일리어싱 (테두리를 먹지 않게 좁게)
        if(A <= 0.003) continue;
        if(A > 1) A = 1;

        const o = rowOff + px*4;
        D[o]   = R8 < 1 ? R8*255 : 255;
        D[o+1] = G8 < 1 ? G8*255 : 255;
        D[o+2] = B8 < 1 ? B8*255 : 255;
        D[o+3] = A*255;
      }
    }
    b.y = yEnd;
    return yEnd >= S;
  }

  // 매 프레임 시간 예산만큼만 이어서 굽는다 → 프레임 드랍 없이 약 0.4초 후 완성
  stepBake(){
    if(this.shellDone) return;
    const t0 = performance.now();
    while(performance.now() - t0 < this.BAKE_MS){
      if(!this.bk) this.bk = this.newBake(this.bakeIdx);
      if(this.bakeRows(this.bk, 26)){
        this.bk.c2.putImageData(this.bk.img, 0, 0);
        this.shell[this.bakeIdx] = this.bk.cvs;
        this.bk = null; this.bakeIdx++;
        if(this.bakeIdx >= this.SHELL_N){ this.shellDone = true; return; }
      }
    }
  }

  // 버블마다 위상을 달리 뽑아 막의 흐름이 서로 동기화되지 않게 한다
  shellSprite(now, seed){
    const a = this.shell; if(!a || !a[0]) return null;
    // 막의 흐름은 아주 천천히 — 빠르게 돌리면 무지개가 일렁여 어지럽다
    let k = Math.floor(now/240 + seed*this.SHELL_N*1.7) % this.SHELL_N;
    if(k < 0) k += this.SHELL_N;
    return a[k] || a[0];
  }

  // ══════════════════════════════════════════════════════════════════
  //  파스텔 셸 렌더러
  //  레퍼런스: 부드러운 역광 아래의 비눗방울 사진. 박막 간섭 줄무늬(무지개)는
  //  보이지 않고, 한 방울이 하나의 파스텔 색을 머금는다. 가운데는 배경이
  //  비칠 만큼 비어 있고 가장자리로 갈수록 색이 짙어지다가 테두리에서
  //  흰빛으로 타오른다. 그 위에 크고 부드러운 하이라이트 몇 개가 얹힌다.
  //
  //  ※ 생성·물리·충돌과는 무관하다. 여기서 바뀌는 것은 '같은 좌표에
  //    무엇을 칠하는가' 뿐이다(절대규칙 1·2).
  // ══════════════════════════════════════════════════════════════════
  // ══════════════════════════════════════════════════════════════════
  //  파스텔 셸 렌더러 — '색이 들어간 유리 공'이 아니라
  //  '빛이 은은하게 스며든 비눗방울'
  //
  //  원칙
  //   · 단색으로 채우지 않는다. 큰 radial gradient 를 여러 겹 겹쳐
  //     핑크·노랑·민트·라벤더가 아주 넓고 흐릿하게 섞이게 한다.
  //   · 합성은 multiply 가 아니라 screen 이다. 색이 쌓일수록 어두워지는 게
  //     아니라 밝아져야 막이 빛을 머금은 것처럼 보인다.
  //   · 각 겹의 불투명도는 0.06~0.18. 배경이 충분히 비쳐야 한다.
  //   · 테두리는 1~2px 의 얇은 밝은 선. 두꺼운 stroke 는 유리구슬이 된다.
  //   · 하이라이트는 왼쪽 위의 넓고 흐릿한 반사 하나 + 아주 약한 곡선 하나.
  //     여러 개 넣으면 반짝이는 구슬이 된다.
  //
  //  ※ 생성·물리·충돌·회전·수명과는 완전히 분리되어 있다. 여기서 하는 일은
  //    '같은 좌표에 무엇을 칠하는가' 뿐이다(절대규칙 1·2).
  // ══════════════════════════════════════════════════════════════════
  SHELL_PALE = 0.12;   // 음정색을 흰빛으로 들어올리는 정도 (파스텔화)  ※ 0.30 → 0.12
  // ── 입체감 (2D 일러스트) ── '맑은 비눗막' 렌더러에서 가져옴. 0이면 평면.
  DEPTH = 1.0;
  SOFT_BLUR  = true;   // ctx.filter 블러 — 경계와 블룸을 부드럽게
  // 오팔 블룸: [색, 불투명도, x오프셋, y오프셋, 반지름] (모두 r 배수)
  OPAL = [
    ['255,178,202', 0.24, -0.28, -0.12, 0.55],
    ['255,230,140', 0.21,  0.28, -0.12, 0.48],
    ['152,225,205', 0.21,  0.10,  0.30, 0.52],
    ['175,195,255', 0.17, -0.12,  0.24, 0.45],
  ];
  // 오팔 림: [시작각, 끝각(π 배수), 색, 불투명도]
  OPAL_RIM = [
    [0.05, 0.55, '255,175,200', 0.62],
    [0.60, 1.00, '255,235,150', 0.54],
    [1.05, 1.42, '155,225,205', 0.48],
    [1.45, 1.85, '180,200,255', 0.44],
  ];
  drawBloom(ctx, bx, by, radius, color, alpha){
    if(radius <= 0 || alpha <= 0.002) return;
    const g = ctx.createRadialGradient(bx, by, 0, bx, by, radius);
    g.addColorStop(0,   'rgba(' + color + ',' + alpha.toFixed(4) + ')');
    g.addColorStop(.45, 'rgba(' + color + ',' + (alpha*0.55).toFixed(4) + ')');
    g.addColorStop(1,   'rgba(' + color + ',0)');
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.arc(bx, by, radius, 0, Math.PI*2); ctx.fill();
  }
  drawSoapCircle(ctx, x, y, r, ar, now, alpha, seed, tone){
    if(this._glCap){ this.gl3dCapture(ctx, x, y, r, ar, now, alpha, seed, tone); return; }
    const sd = seed || 0;
    const hasTone = (tone !== undefined && tone !== null);
    const tn = Math.max(-1, Math.min(1, tone || 0));
    // 지금 발화한 음의 색. 순수 스펙트럼색은 채도가 너무 높으므로 파스텔로 낮춘다.
    const C = hasTone ? this.famPale(tn, this.SHELL_PALE) : [198, 226, 218];
    const rC = C[0]|0, gC = C[1]|0, bC = C[2]|0, TC = rC+','+gC+','+bC;
    // 표면장력 진동 — 그리는 반지름에만 곱한다. 물리 반지름 r 은 불변.
    const w1 = 1 + Math.sin(now/430 + sd*5.1)*0.010 + Math.sin(now/197 + sd*2.3)*0.004;
    const w2 = 1 + Math.sin(now/355 + sd*8.7 + 1.7)*0.009 + Math.cos(now/223 + sd*4.1)*0.004;
    const rx = r/Math.sqrt(ar)*w1, ry = r*Math.sqrt(ar)*w2;
    const R  = Math.max(rx, ry);
    const attachment=this.soapAttachment;
    const milk=attachment?1:.42;
    const depth=attachment?0:this.DEPTH; // Preserve the original continuous film while attached.
    const path = (k)=>{ ctx.beginPath();
      if(attachment) this.connectedSoapPath(ctx,rx,ry,sd,now,k,{
        x:attachment.x-x,y:attachment.y-y,aperture:attachment.aperture,rimX:attachment.rimX,skew:attachment.skew,ux:attachment.ux,uy:attachment.uy,vx:attachment.vx,vy:attachment.vy,progress:attachment.progress});
      else this.blobPath(ctx,0,0,rx,ry,sd,now,k);
    };
    // 발성 길이 → 막의 농도. 매핑의 의미는 그대로, 범위만 이 렌더러에 맞췄다.
    const fill = Math.max(0, Math.min(1, alpha));
    const dens = 0.50 + 0.50*Math.pow(fill, 1.15);
    // 블러는 큰 방울에서만 의미가 있고 비싸다. 작은 방울은 그냥 넘긴다.
    const blur = (this.SOFT_BLUR && R > 22);

    ctx.save(); ctx.translate(x, y);
    // ── 0. 바깥 헤일로 ──
    // 방울 둘레에 아주 옅은 빛이 한 겹 번진다. 경계를 딱딱하게 만들지 않으면서
    // 배경에서 방울을 떼어 놓는다 — 그림자가 아니라 빛이므로 무겁지 않다.
    ctx.save();
    ctx.globalCompositeOperation = 'screen';
    if(blur) ctx.filter = 'blur(' + Math.max(2, R*0.10).toFixed(2) + 'px)';
    const gH = ctx.createRadialGradient(0, 0, R*0.80, 0, 0, R*1.20);
    gH.addColorStop(0,   'rgba(255,255,255,0)');
    gH.addColorStop(.42, 'rgba(255,255,255,' + (0.34*dens*milk).toFixed(3) + ')');
    gH.addColorStop(1,   'rgba(255,255,255,0)');
    ctx.fillStyle = gH;
    if(!attachment){ctx.beginPath();ctx.arc(0,0,R*1.20,0,Math.PI*2);ctx.fill();}
    ctx.restore();

    // ── 0.5 그림자 ──
    // 방울이 공간 속에 떠 있다는 것을 알려 주는 건 방울 자체보다 그 아래의 옅은
    // 그늘이다. 아래로 조금 내려 찍고, multiply 로 배경을 살짝 어둡힌다.
    if(depth > 0 && !attachment){
      ctx.save();
      ctx.globalCompositeOperation = 'multiply';
      if(blur) ctx.filter = 'blur(' + Math.max(3, R*0.16).toFixed(2) + 'px)';
      const gS = ctx.createRadialGradient(R*0.06, R*0.26, R*0.10, R*0.06, R*0.26, R*1.02);
      gS.addColorStop(0,   'rgba(' + TC + ',' + (0.07*dens*depth).toFixed(3) + ')');
      gS.addColorStop(.55, 'rgba(24,70,62,' + (0.04*dens*depth).toFixed(3) + ')');
      gS.addColorStop(1,   'rgba(24,70,62,0)');
      ctx.fillStyle = gS;
      ctx.beginPath(); ctx.ellipse(R*0.06, R*0.26, R*1.02, R*0.92, 0, 0, Math.PI*2); ctx.fill();
      ctx.restore();
    }

    ctx.save(); path(); ctx.clip();          // 모든 겹은 윤곽 안쪽에만

    // ── 1. 광량 ──
    // 방울은 배경을 '물들이는' 것이 아니라 '밝히며 물들인다'. 이 한 겹이 없으면
    // 옅은 파스텔이 배경과 섞여 탁해지고, 방울이 배경에 눌린다.
    path();
    const gL = ctx.createRadialGradient(-rx*0.20, -ry*0.24, R*0.05, 0, 0, R*1.06);
    gL.addColorStop(0,   'rgba(255,255,255,' + (0.17*dens*milk).toFixed(3) + ')');
    gL.addColorStop(.58, 'rgba(255,255,255,' + (0.22*dens*milk).toFixed(3) + ')');
    gL.addColorStop(1,   'rgba(255,255,255,' + (0.46*dens*milk).toFixed(3) + ')');
    ctx.fillStyle = gL; ctx.fill();

    // ── 2. 내부 색 ──
    // 중심은 밝고 투명하게, 가장자리로 갈수록 음정색이 조금 더 느껴지게.
    const base = ctx.createRadialGradient(-rx*0.15, -ry*0.20, R*0.05, 0, 0, R);
    base.addColorStop(0,   'rgba(255,255,255,' + (0.12*dens*milk).toFixed(3) + ')');
    base.addColorStop(.45, 'rgba(255,255,255,' + (0.08*dens*milk).toFixed(3) + ')');
    base.addColorStop(.78, 'rgba(' + TC + ',' + (0.30*dens).toFixed(3) + ')');
    base.addColorStop(1,   'rgba(' + TC + ',' + (0.52*dens).toFixed(3) + ')');
    ctx.fillStyle = base; path(); ctx.fill();

    // ── 2.5 림 섀도 ──
    // 진짜 비눗방울의 입체감은 가장자리 바로 안쪽의 얇고 어두운 띠에서 온다.
    // 빛이 오는 왼쪽 위는 얇고, 반대편 오른쪽 아래는 두껍고 짙다.
    if(depth > 0){
      ctx.save();
      ctx.globalCompositeOperation = 'multiply';
      if(blur) ctx.filter = 'blur(' + Math.max(1, R*0.035).toFixed(2) + 'px)';
      const gE = ctx.createRadialGradient(-rx*0.22, -ry*0.24, R*0.55, 0, 0, R*1.0);
      gE.addColorStop(0,   'rgba(' + TC + ',0)');
      gE.addColorStop(.62, 'rgba(' + TC + ',0)');
      gE.addColorStop(.86, 'rgba(' + TC + ',' + (0.16*dens*depth).toFixed(3) + ')');
      gE.addColorStop(.96, 'rgba(30,72,66,' + (0.09*dens*depth).toFixed(3) + ')');
      gE.addColorStop(1,   'rgba(30,72,66,' + (0.05*dens*depth).toFixed(3) + ')');
      ctx.fillStyle = gE; path(); ctx.fill();
      ctx.restore();
      // 림 섀도 안쪽에 한 번 더 밝힘 — 띠가 '테두리에 붙은 어둠'으로 읽히게
      ctx.save();
      ctx.globalCompositeOperation = 'screen';
      const gI = ctx.createRadialGradient(0, 0, R*0.60, 0, 0, R*0.88);
      gI.addColorStop(0, 'rgba(255,255,255,0)');
      gI.addColorStop(1, 'rgba(255,255,255,' + (0.14*dens*depth*milk).toFixed(3) + ')');
      ctx.fillStyle = gI; path(); ctx.fill();
      ctx.restore();
    }

    // ── 3. 오팔 컬러 블룸 ──
    // 얼룩이 아니라 '아주 넓고 흐릿하게 섞인 무지갯빛'이어야 한다.
    // 위치를 방울마다 seed 로 조금씩 돌려 두 방울이 같은 무늬를 갖지 않게 한다.
    ctx.save();
    ctx.globalCompositeOperation = 'screen';
    if(blur) ctx.filter = 'blur(' + (R*0.04).toFixed(2) + 'px)';
    const th = sd*1.7;
    const cs = Math.cos(th), sn = Math.sin(th);
    for(const [col, a, ox, oy, rad] of this.OPAL){
      this.drawBloom(ctx, rx*(ox*cs - oy*sn), ry*(ox*sn + oy*cs), R*rad, col, a*dens);
    }
    // 지금 내는 음의 색도 한 겹 — 오팔에 묻히지 않을 만큼만.
    // 이 한 줄이 '음정 → 색' 매핑을 화면에서 지킨다.
    this.drawBloom(ctx, rx*0.04*cs, ry*0.12*sn, R*0.70, TC, 0.42*dens);
    ctx.restore();

    // ── 5. 하이라이트 ──
    // 왼쪽 위의 넓고 흐릿한 반사 하나. 작고 날카로운 점은 유리구슬이 된다.
    ctx.save();
    ctx.globalCompositeOperation = 'screen';
    if(blur) ctx.filter = 'blur(' + Math.max(1, R*0.02).toFixed(2) + 'px)';
    const hx = -rx*0.32, hy = -ry*0.32;
    const h = ctx.createRadialGradient(hx, hy, 0, hx, hy, R*0.28);
    h.addColorStop(0,  (attachment?'rgba(255,255,255,0.92)':'rgba(255,255,255,.72)'));
    h.addColorStop(.3, (attachment?'rgba(255,255,255,0.52)':'rgba(255,255,255,.30)'));
    h.addColorStop(1,  'rgba(255,255,255,0)');
    ctx.fillStyle = h;
    ctx.beginPath();
    if(ctx.ellipse) ctx.ellipse(hx, hy, R*0.20, R*0.11, -0.65, 0, Math.PI*2);
    else            ctx.arc(hx, hy, R*0.16, 0, Math.PI*2);
    ctx.fill();
    // 아주 약한 곡선 반사 하나 더 — 곡면임을 알려 줄 정도로만
    ctx.strokeStyle = 'rgba(255,255,255,0.22)';
    ctx.lineWidth = Math.max(1, R*0.030);
    ctx.lineCap = 'round';
    ctx.beginPath();
    ctx.arc(0, 0, R*0.74, Math.PI*1.02, Math.PI*1.34);
    ctx.stroke();
    if(depth > 0){
      // 하이라이트 심지 — 넓은 반사 안에 조금 더 또렷한 점 하나. 곡면의 정점.
      const hc = ctx.createRadialGradient(hx-R*0.02, hy-R*0.02, 0, hx-R*0.02, hy-R*0.02, R*0.10);
      hc.addColorStop(0, 'rgba(255,255,255,' + (0.95*depth).toFixed(3) + ')');
      hc.addColorStop(1, 'rgba(255,255,255,0)');
      ctx.fillStyle = hc;
      ctx.beginPath(); ctx.ellipse(hx-R*0.02, hy-R*0.02, R*0.085, R*0.05, -0.65, 0, Math.PI*2); ctx.fill();
      // 두 번째 반사 — 빛의 반대편, 오른쪽 아래 림 안쪽에 걸린 작은 초승달.
      // 구가 뒤에서도 빛을 받고 있다는 신호. 이게 없으면 반원으로 읽힌다.
      ctx.strokeStyle = 'rgba(255,255,255,' + (0.40*dens*depth).toFixed(3) + ')';
      ctx.lineWidth = Math.max(1.2, R*0.030);
      ctx.beginPath();
      ctx.arc(0, 0, R*0.84, Math.PI*0.12, Math.PI*0.42);
      ctx.stroke();
      ctx.strokeStyle = 'rgba(255,255,255,' + (0.18*dens*depth).toFixed(3) + ')';
      ctx.lineWidth = Math.max(2, R*0.060);
      ctx.beginPath();
      ctx.arc(0, 0, R*0.80, Math.PI*0.16, Math.PI*0.38);
      ctx.stroke();
    }
    ctx.restore();

    // ── 4. 가장자리 오팔 림 ──
    // 전체를 무지개로 두르지 않는다. 원의 일부에만 빛이 걸린 느낌.
    ctx.save();
    ctx.globalCompositeOperation = 'screen';
    ctx.lineCap = 'round';
    for(const [a0, a1, col, al] of this.OPAL_RIM){
      ctx.strokeStyle = 'rgba(' + col + ',' + (al*dens).toFixed(3) + ')';
      ctx.lineWidth = Math.max(1.5, R*0.022);
      ctx.beginPath();
      ctx.arc(0, 0, R*0.975, Math.PI*a0 + th, Math.PI*a1 + th);
      ctx.stroke();
    }
    ctx.restore();
    ctx.restore();                            // 클립 해제

    // ── 1. 외곽선 ──
    // 1~2px 의 아주 얇은 밝은 림. 두꺼운 stroke 금지.
    ctx.save();
    ctx.globalCompositeOperation = 'screen';
    if(blur) ctx.filter = 'blur(' + Math.max(0.4, R*0.004).toFixed(2) + 'px)';
    ctx.strokeStyle = 'rgba(255,255,255,0.88)';
    ctx.lineWidth = Math.max(1, R*0.013);
    path(0.99); ctx.stroke();
    // 그 바로 안쪽에 한 겹 더 옅게 — 두께를 늘리지 않고 림만 밝힌다
    ctx.strokeStyle = 'rgba(255,255,255,0.34)';
    ctx.lineWidth = Math.max(1, R*0.030);
    path(0.962); ctx.stroke();
    if(depth > 0 && !attachment){
      // 프레넬 — 빛의 반대편(오른쪽 아래)으로 갈수록 테두리가 두껍고 밝다.
      // 균일한 링은 원반, 한쪽이 두꺼운 링은 공.
      ctx.lineCap = 'round';
      const segs = 14;
      for(let i=0;i<segs;i++){
        const a0 = Math.PI*(0.0 + i*0.9/segs), a1 = Math.PI*(0.0 + (i+1)*0.9/segs) + 0.02;
        const mid = (a0+a1)/2;
        const k = 0.5 + 0.5*Math.cos(mid - Math.PI*0.35);   // 0.35π(오른쪽 아래)에서 최대
        ctx.strokeStyle = 'rgba(255,255,255,' + (0.38*k*dens*depth).toFixed(3) + ')';
        ctx.lineWidth = Math.max(1, R*(0.008 + 0.022*k));
        ctx.beginPath();
        for(let j=0;j<=5;j++){
          const th=a0+(a1-a0)*j/5,shape=this.blobK(th,sd,now)*.968;
          const px=Math.cos(th)*rx*shape,py=Math.sin(th)*ry*shape;
          if(j===0)ctx.moveTo(px,py);else ctx.lineTo(px,py);
        }
        ctx.stroke();
      }
    }
    ctx.restore();

    ctx.restore();
  }

  drawGlyph(ctx, s, sh){
    const a = Math.min(1,(s.alpha*.28+.72))*sh;
    if(this._glCap){
      ctx.lineJoin = 'round';
      ctx.shadowColor = 'rgba(255,255,255,.95)'; ctx.shadowBlur = Math.max(8, s.r*0.24);
      ctx.strokeStyle = 'rgba(255,255,255,'+(0.9*a).toFixed(3)+')'; ctx.lineWidth = Math.max(3, s.r*0.09);
      ctx.strokeText(s.v, 0, 0);
      ctx.shadowBlur = 0;
      ctx.fillStyle = 'rgba(19,64,60,'+a.toFixed(3)+')';
      ctx.fillText(s.v, 0, 0);
      return;
    }
    ctx.shadowColor = 'rgba(28,72,60,0.34)';
    ctx.shadowBlur = Math.max(5, s.r*0.14);
    ctx.fillStyle = 'rgba(255,255,255,'+a.toFixed(3)+')';
    ctx.fillText(s.v, 0, 0);
    ctx.shadowBlur = 0; ctx.fillText(s.v, 0, 0);
  }
  drawSeg(ctx, x, y, s, now, alpha, letter){
    this.drawSoapCircle(ctx, x, y, s.r, s.ar, now, alpha*s.alpha, s.seed, s.tone);
    if(letter && s.v){
      // 글자는 음정 속도로 입체 회전한다. 방울(막·좌표)은 돌지 않는다 — 그리는 값만.
      ctx.save();
      const sh = this.applySpin3D(ctx, x, y, s, now);
      ctx.font = `800 ${Math.max(19, s.r*.78)}px ${this.UIFONT}`;
      ctx.textAlign='center'; ctx.textBaseline='middle';
      this.drawGlyph(ctx, s, sh);
      ctx.textBaseline='alphabetic';
      ctx.restore();
    }
  }

  drawPeanut(ctx, b, now, attachment=null){
    const ps = this.layoutSegs(b.segs);
    const n = b.segs.length;
    b.segs.forEach((s,i)=>{
      // 같은 모음으로 이어진 이웃의 내부 윤곽을 잘라내 하나의 땅콩 덩어리로
      const ex=[];
      if(i>0 && s.v && b.segs[i-1].v===s.v) ex.push(i-1);
      if(i<n-1 && s.v && b.segs[i+1].v===s.v) ex.push(i+1);
      ctx.save();
      if(ex.length){
        ctx.beginPath();
        ctx.rect(-9999,-9999,19998,19998);
        for(const j of ex){
          const o=b.segs[j], p=ps[j];
          this.blobPath(ctx,p.x,p.y,Math.max(1,o.r/Math.sqrt(o.ar)-1),Math.max(1,o.r*Math.sqrt(o.ar)-1),o.seed||0,now);
        }
        ctx.clip('evenodd');
      }
      this._gl3dOwner = b.__owner || b;
      this.soapAttachment = attachment && i===this.soapPort(b).idx ? attachment : null;
      if(!s.v){
        // 인식불가 표면 효과: 미세 떨림 or 한쪽으로 부풀었다 줄어듦
        const t = now/1000, seed = s.seed||0;
        let dr = 0, dar = 1, dx = 0;
        if(s.sfx==='trem'){ dr = Math.sin(now/24+seed*9)*s.r*.015 + Math.sin(now/41+seed)*s.r*.012; }
        else { const k = Math.sin(now/380+seed); dar = 1 + k*.16; dx = k*s.r*.1; }
        this.drawSeg2(ctx, ps[i].x+dx, ps[i].y, s, s.r+dr, s.ar*dar, now);
        this.drawInnerFx(ctx, ps[i].x+dx, ps[i].y, s, now);
      } else {
        this.drawSeg(ctx, ps[i].x, ps[i].y, s, now, 1, false);
      }
      ctx.restore();
    });
    this.soapAttachment = null;
    // 플라토 경계벽: 두 막이 맞닿은 접촉면에 생기는 공유 막
    // (배치 좌표는 건드리지 않고, 이웃 타원의 호를 현재 타원 안쪽으로만 그린다)
    for(let i=1;i<n;i++){
      const s = b.segs[i], o = b.segs[i-1];
      if(!s.v || o.v !== s.v || this._glCap) continue;   // 3D 에서는 겹친 구가 실제 공유 막을 만든다
      const p = ps[i], q = ps[i-1];
      ctx.save();
      ctx.beginPath();
      this.blobPath(ctx, p.x, p.y, s.r/Math.sqrt(s.ar), s.r*Math.sqrt(s.ar), s.seed||0, now);
      ctx.clip();
      ctx.beginPath();
      this.blobPath(ctx, q.x, q.y, o.r/Math.sqrt(o.ar), o.r*Math.sqrt(o.ar), o.seed||0, now);
      ctx.strokeStyle = 'rgba(255,255,255,.42)'; ctx.lineWidth = 1.2; ctx.stroke();
      ctx.strokeStyle = 'rgba(255,255,255,.20)'; ctx.lineWidth = .7; ctx.stroke();
      ctx.restore();
    }
    // 글자는 클리핑 없이 위에 — 인식불가 세그먼트는 이름 없는 소리가 웅얼거리는 표식
    b.segs.forEach((s,i)=>{
      ctx.textAlign='center'; ctx.textBaseline='middle';
      if(s.v){
        // Apple · Clarity: 막이 화려해진 만큼 글자 뒤에 종이색 헤일로를 깔아 대비 확보
        ctx.save();
        // 글자는 음정 속도로 입체 회전한다 — 방울 자체는 돌지 않는다.
        const sh = this.applySpin3D(ctx, ps[i].x, ps[i].y, s, now);
        ctx.font = `800 ${Math.max(19, s.r*.78)}px ${this.UIFONT}`;
        // 흰 글자. 그림자는 검정이 아니라 짙은 세이지로, 넓고 옅게 깔아
        // 파스텔 막 위에서도 글자가 배경에 묻히지 않게 한다.
        this.drawGlyph(ctx, s, sh);
        ctx.restore();
      }
      // 인식불가 세그먼트는 글자 없이 표면·내면 효과만 (구조도: 글자없이 비눗방울만 제시)
      ctx.textBaseline='alphabetic';
    });
  }

  drawSeg2(ctx, x, y, s, r, ar, now){
    this.drawSoapCircle(ctx, x, y, r, ar, now, s.alpha, s.seed, s.tone);
  }

  // 인식불가 내면 효과: 빙글빙글 소용돌이 or 작은 거품이 기포처럼 차오름
  drawInnerFx(ctx, x, y, s, now){
    const rx = s.r/Math.sqrt(s.ar), ry = s.r*Math.sqrt(s.ar);
    ctx.save();
    ctx.beginPath(); this.blobPath(ctx, x, y, rx, ry, s.seed||0, now, .94); ctx.clip();
    if(s.ifx==='swirl') this.drawVortex(ctx, x, y, rx, ry, s, now);
    else                this.drawFizz(ctx, x, y, rx, ry, s, now);
    ctx.restore();
  }

  // ── 인식불가: 소용돌이 ────────────────────────────────────────
  // 이름을 얻지 못한 소리가 막 안에서 휘몰아친다. 선을 여러 겹 두르면
  // 나이테가 되어 버리므로, 폭이 변하는 '리본' 두 갈래를 채워서 그린다.
  // 중심으로 갈수록 좁아지며 빨려 들어가고, 가운데에는 눈이 남는다.
  drawVortex(ctx, x, y, rx, ry, s, now){
    const seed = s.seed || 0, R = Math.min(rx, ry);
    const rot = now/2700 + seed*2.3;
    const arm = (a0, turn, wMax, alpha, dir) => {
      const N = 64, px = [], py = [], hw = [];
      for(let i = 0; i <= N; i++){
        const t = i/N;
        const th = a0 + dir*t*turn;
        const r  = 0.135 + 0.855*Math.pow(t, 0.84);
        px.push(x + Math.cos(th)*r*rx);
        py.push(y + Math.sin(th)*r*ry);
        // 중심에서 실낱 → 중간에서 최대 → 바깥에서 다시 흩어진다
        hw.push(Math.sin(Math.pow(t, 0.60)*Math.PI)*wMax*R + 0.004*R);
      }
      const nrm = i => {
        const i2 = i < N ? i+1 : N, i0 = i > 0 ? i-1 : 0;
        let dx = px[i2]-px[i0], dy = py[i2]-py[i0];
        const L = Math.hypot(dx, dy) || 1;
        return [-dy/L*hw[i], dx/L*hw[i]];
      };
      ctx.beginPath();
      for(let i = 0; i <= N; i++){ const n = nrm(i);
        if(i === 0) ctx.moveTo(px[i]+n[0], py[i]+n[1]); else ctx.lineTo(px[i]+n[0], py[i]+n[1]); }
      for(let i = N; i >= 0; i--){ const n = nrm(i); ctx.lineTo(px[i]-n[0], py[i]-n[1]); }
      ctx.closePath();
      const g = ctx.createRadialGradient(x, y, 0, x, y, Math.max(rx, ry));
      g.addColorStop(0,  'rgba(255,255,255,' + (0.92*alpha).toFixed(3) + ')');
      g.addColorStop(.34,'rgba(240,253,249,' + (0.55*alpha).toFixed(3) + ')');
      g.addColorStop(.72,'rgba(176,231,217,' + (0.30*alpha).toFixed(3) + ')');
      g.addColorStop(1,  'rgba(176,231,217,0)');
      ctx.fillStyle = g; ctx.fill();
    };
    const TAU = Math.PI*2;
    // 넓고 옅은 바닥 층을 먼저 깔아 '그려진 도형'이 아니라
    // 흘러가는 막처럼 보이게 한다
    arm(rot - 0.10,      TAU*1.26, 0.330, 0.34,  1);
    arm(rot + TAU*0.5 - 0.10, TAU*1.26, 0.330, 0.34, 1);
    arm(rot,             TAU*1.22, 0.190, 1.10,  1);
    arm(rot + TAU*0.5,   TAU*1.22, 0.190, 1.10,  1);
    arm(rot + TAU*0.27,  TAU*1.06, 0.090, 0.62,  1);
    arm(rot + TAU*0.77,  TAU*1.06, 0.090, 0.62,  1);
    // 소용돌이의 눈 — 안쪽은 비고 테두리가 밝다
    const er = R*0.22;
    const ge = ctx.createRadialGradient(x, y, er*0.10, x, y, er);
    ge.addColorStop(0,  'rgba(168,222,208,.30)');
    ge.addColorStop(.62,'rgba(255,255,255,.80)');
    ge.addColorStop(1,  'rgba(255,255,255,0)');
    ctx.fillStyle = ge;
    ctx.beginPath(); ctx.arc(x, y, er, 0, 7); ctx.fill();
  }

  // ── 세미 버블: 인식이 되다 말 때의 "꼬르르륵" ──────────────────
  // 막 안에서 잔 기포가 줄지어 올라온다. 각각은 속이 빈 유리 방울이고,
  // 올라가며 커지다가 천장에 닿기 직전 얇아져 사라진다.
  drawFizz(ctx, x, y, rx, ry, s, now){
    const seed = s.seed || 0, R = Math.min(rx, ry);
    const K = R < 30 ? 5 : 7;
    // 바닥에서 피어오르는 젖빛 기둥
    const gp = ctx.createRadialGradient(x, y + ry*0.95, R*0.06, x, y + ry*0.95, ry*1.5);
    gp.addColorStop(0,  'rgba(255,255,255,.72)');
    gp.addColorStop(.42,'rgba(214,246,238,.34)');
    gp.addColorStop(1,  'rgba(214,246,238,0)');
    ctx.fillStyle = gp;
    ctx.beginPath(); ctx.ellipse(x, y + ry*0.6, rx*0.72, ry*0.95, 0, 0, 7); ctx.fill();

    for(let k = 0; k < K; k++){
      const sp = 0.66 + ((k*37) % 11)/11*0.58;                 // 개별 상승 속도
      const ph = (((now/3100)*sp + k*0.6180339 + seed) % 1 + 1) % 1;
      const lane = Math.sin(k*2.3999 + seed*3.1);
      const bx = x + lane*rx*0.36 + Math.sin(ph*5.0 + k*1.7)*rx*0.075;
      const by = y + ry*0.86 - ph*ry*1.74;
      const br = (0.070 + 0.080*((k % 3)/2))*R*(0.68 + 0.50*ph);
      const fade = Math.min(1, ph*6.5)*Math.min(1, (1 - ph)*3.6);
      if(fade <= 0.02 || br < 1.1) continue;
      // 속이 빈 유리 방울: 테두리가 밝고 좌상단에 점 하이라이트
      const gb = ctx.createRadialGradient(bx, by, br*0.10, bx, by, br);
      gb.addColorStop(0,   'rgba(255,255,255,' + (0.10*fade).toFixed(3) + ')');
      gb.addColorStop(.58, 'rgba(214,246,238,' + (0.14*fade).toFixed(3) + ')');
      gb.addColorStop(.84, 'rgba(255,255,255,' + (0.72*fade).toFixed(3) + ')');
      gb.addColorStop(1,   'rgba(150,222,206,' + (0.42*fade).toFixed(3) + ')');
      ctx.fillStyle = gb;
      ctx.beginPath(); ctx.arc(bx, by, br, 0, 7); ctx.fill();
      if(br > 2.4){
        ctx.fillStyle = 'rgba(255,255,255,' + (0.9*fade).toFixed(3) + ')';
        ctx.beginPath(); ctx.arc(bx - br*0.34, by - br*0.36, br*0.20, 0, 7); ctx.fill();
      }
    }
  }

  // ── 막대(완드) ─────────────────────────────────────────────────────
  // 생성 공간 바닥에서 올라온 얇은 대와, 그 끝의 고리. 방울은 이 고리에서만
  // 태어난다. 고리는 살짝 위에서 내려다본 타원 — 그래야 방울이 고리 '위로'
  // 부풀어 오르는 것으로 읽힌다.
  WAND_R = 26;          // 고리 반지름(px)
  WAND_RY = 0.62;       // 고리 타원 세로 비율 (원근)
  connectedSoapPath(ctx,rx,ry,seed,now,k,a){
    const scale=k===undefined?1:k,cut=.94;
    const point=t=>{const r=this.blobK(t,seed,now)*scale;return {x:Math.cos(t)*rx*r,y:Math.sin(t)*ry*r};};
    const top=point(-cut),bottom=point(cut);
    ctx.moveTo(bottom.x,bottom.y);
    for(let i=1;i<=64;i++){
      const p=point(cut+(Math.PI*2-cut*2)*i/64);ctx.lineTo(p.x,p.y);
    }
    const ex=a.x*scale,ey=a.y*scale,opening=a.aperture*scale;
    const length=Math.max(8,ex-top.x),mx=top.x+length*.57;
    const cy=ey*.58,pinch=Math.pow(1-Math.min(1,a.progress),1.6);
    // A slender continuous film while voiced, narrowing further on release.
    const waist=Math.max(.25,Math.min(ry*.46,opening*.72)*pinch);
    const rimX=(a.rimX||opening*.45)*scale,skew=(a.skew||0)*scale;
    const ux=(a.ux===undefined?rimX/scale:a.ux)*scale,uy=(a.uy||0)*scale;
    const vx=(a.vx===undefined?skew/scale:a.vx)*scale,vy=(a.vy===undefined?opening/scale:a.vy)*scale;
    const tx=ex-vx,ty=ey-vy,bx=ex+vx,by=ey+vy;
    ctx.bezierCurveTo(top.x+length*.27,top.y+length*.08,mx-length*.16,cy-waist,mx,cy-waist);
    ctx.bezierCurveTo(mx+length*.2,cy-waist,tx-length*.14,ty,tx,ty);
    ctx.bezierCurveTo(tx+ux*.552,ty+uy*.552,ex+ux-vx*.552,ey+uy-vy*.552,ex+ux,ey+uy);
    ctx.bezierCurveTo(ex+ux+vx*.552,ey+uy+vy*.552,bx+ux*.552,by+uy*.552,bx,by);
    ctx.bezierCurveTo(bx-length*.14,by,mx+length*.2,cy+waist,mx,cy+waist);
    ctx.bezierCurveTo(mx-length*.16,cy+waist,bottom.x+length*.27,bottom.y-length*.08,bottom.x,bottom.y);
    ctx.closePath();
  }
  soapPort(b){
    const ps=this.layoutSegs(b.segs);let idx=0;
    for(let i=1;i<ps.length;i++) if(ps[i].x+b.segs[i].r>ps[idx].x+b.segs[idx].r) idx=i;
    const r=b.segs[idx].r;
    return {x:ps[idx].x+r*.68,y:ps[idx].y,r:r*.65,idx};
  }
  wandCenterOffset = 120;
  // ── 막대 기준 위치 ──
  // 화자 한 명: 왼쪽 하단 모서리에서 나온다. (나중에 두 명이 되면 오른쪽에도
  // 하나 더 두고 WAND_SIDE 를 화자별로 넘긴다.)  0.5 면 예전처럼 가운데.
  // ※ 장면 전체가 drawScene 에서 좌우 반전(translate(W,0); scale(-1,1))되어 그려지므로
  //   여기 좌표는 '원본 좌표'다 — 0.80 이 화면에서는 왼쪽 약 20% 지점이 되고,
  //   거기서 wandCenterOffset 만큼 더 왼쪽으로 간다. 화면 왼쪽 = 원본 값을 키운다.
  WAND_SIDE = 0.80;
  wandBaseX(W){ return W*this.WAND_SIDE; }
  centeredWandAnchor(W,now){
    if(this.cur){
      const age=Math.max(0,now-this.cur.t0);
      const t=age/470,p=1-Math.exp(-t)*(1+t),ti=age/190,sx=.26+.74*(1-Math.exp(-ti)*(1+ti));
      const live={segs:this.cur.segs.map(s=>({...s,r:this.segRadius(s.lvl)}))};
      // Translate the whole reference arrangement; never stretch its connecting film.
      this.wandCenterOffset=this.soapPort(live).x*sx+8+76*p;
    }
    // 화면 왼쪽 가장자리에서 40px 안쪽을 넘지 않게 (반전 후 x = W - 값)
    return Math.min(W-40, this.wandBaseX(W)+this.wandCenterOffset);
  }
  soapPose(b,ax,ay,age){
    // 원래 궤적 그대로 — 출발만 S곡선으로 (첫 프레임에 툭 튀어나오지 않게)
    const t=Math.max(0,age)/470, p=1-Math.exp(-t)*(1+t), port=this.soapPort(b);
    return {x:ax-port.x-8-76*p,y:ay-port.y-22*p,p};
  }
  // Visual-only head size follows the same radius used by the live bubble.
  wandHeadScale = 1;
  stepWandHead(now,dt){
    const seg=this.cur && this.cur.segs[this.cur.segs.length-1];
    let target=1;
    if(seg){
      const radius=this.segRadius(seg.lvl);
      target=Math.max(.4,radius/60);
    } else if(this.anchorBorn && now-this.anchorBorn<320){
      return; // Keep the aperture steady until the attached film has detached.
    }
    const blend=1-Math.exp(-Math.max(0,dt)/(seg?110:360));
    this.wandHeadScale+=(target-this.wandHeadScale)*blend;
  }
  wandAngle=.24; wandBend=.06; wandPivotX=0; wandPivotY=0;
  stepWandMotion(ax,ay,H,now,dt){
    const seg=this.cur && this.cur.segs[this.cur.segs.length-1];
    const releasing=!seg && this.anchorBorn && now-this.anchorBorn<320;
    const level=seg?Math.max(0,Math.min(1,seg.lvl)):0;
    // Let a louder voice visibly lay the wand down and flex its shaft.
    const strength=Math.sqrt(level);
    const target=.24+.48*strength;
    const bendTarget=.06+.22*strength;
    if(!releasing){
      const k=1-Math.exp(-Math.max(0,dt)/240);
      this.wandAngle+=(target-this.wandAngle)*k;
      this.wandBend+=(bendTarget-this.wandBend)*k;
    }
    this.wandPivotY=H-8;
    this.wandPivotX=ax-(this.wandPivotY-ay)*Math.tan(this.wandAngle);
  }
  wandFilmAxes(sx=1,sy=1,rotation=0){
    const t=this.wandAngle-.12-rotation,hs=this.wandHeadScale;
    return {ux:13*hs*Math.cos(t)/sx,uy:13*hs*Math.sin(t)/sy,
      vx:-29*hs*Math.sin(t)/sx,vy:29*hs*Math.cos(t)/sy};
  }
  wandShaftCurve(jx,jy,theta){
    const dx=jx-this.wandPivotX,dy=jy-this.wandPivotY;
    const length=Math.max(1,Math.hypot(dx,dy)),bend=length*this.wandBend;
    // The lower shaft bows; the upper tangent meets the tilted head smoothly.
    return {c1x:this.wandPivotX+dx*.28+dy/length*bend,
      c1y:this.wandPivotY+dy*.38-dx/length*bend,
      c2x:jx-Math.sin(theta)*length*.28,
      c2y:jy+Math.cos(theta)*length*.28};
  }
  drawWand(ctx, ax, ay, H, now, frontOnly=false){
    const hs=this.wandHeadScale;
    if(this._glCap && !frontOnly){
      const m=ctx.getTransform(),dpr=devicePixelRatio,p=m.transformPoint(new DOMPoint(ax,ay));
      const a=this.wandFilmAxes();
      const vector=(x,y)=>[(m.a*x+m.c*y)/dpr,-(m.b*x+m.d*y)/dpr,0];
      this._wandGLFrame={u:vector(a.ux,a.uy),v:vector(a.vx,a.vy)};
      this.gl3d.wand(p.x/dpr,p.y/dpr,hs,H,{overlay:true,u:this._wandGLFrame.u,v:this._wandGLFrame.v});
    }
    ctx.save();ctx.lineCap='round';
    const gold=ctx.createLinearGradient(ax-20,ay,ax+24,ay+12);
    gold.addColorStop(0,'#82b7c8');gold.addColorStop(.22,'#c8ecf1');gold.addColorStop(.46,'#f5ffff');gold.addColorStop(.67,'#e6d5eb');gold.addColorStop(.84,'#d6f0e9');gold.addColorStop(1,'#95c5ce');
    if(!frontOnly){
    const theta=this.wandAngle-.12;
    const jx=ax-Math.sin(theta)*32*hs,jy=ay+Math.cos(theta)*32*hs;
    const shaft=ctx.createLinearGradient(this.wandPivotX-6,0,this.wandPivotX+6,0);
    shaft.addColorStop(0,'#88b8c8');shaft.addColorStop(.45,'#edffff');shaft.addColorStop(1,'#b9dce2');
    const shaftPath=(offset)=>{
      ctx.beginPath();ctx.moveTo(this.wandPivotX+offset,this.wandPivotY);
      ctx.lineTo(jx+offset,jy);
    };
    ctx.strokeStyle=shaft;ctx.lineWidth=11;shaftPath(0);ctx.stroke();
    ctx.strokeStyle='rgba(255,255,255,.94)';ctx.lineWidth=2;shaftPath(-2);ctx.stroke();
    }
    ctx.translate(ax,ay);ctx.rotate(this.wandAngle);ctx.scale(hs,hs);ctx.translate(-ax,-ay);
    if(frontOnly){
      ctx.strokeStyle=gold;ctx.lineWidth=8;
      ctx.beginPath();ctx.ellipse(ax,ay,15,34,-.12,-Math.PI/2,Math.PI/2);ctx.stroke();
      ctx.strokeStyle='rgba(255,255,255,.82)';ctx.lineWidth=1.5;
      ctx.beginPath();ctx.ellipse(ax+1,ay,15,34,-.12,-Math.PI/2,Math.PI*.15);ctx.stroke();
      ctx.restore();return;
    }
    ctx.shadowColor='rgba(75,128,148,.17)';ctx.shadowBlur=7;ctx.shadowOffsetX=3;
    ctx.strokeStyle=gold;ctx.lineWidth=8;
    ctx.beginPath();ctx.ellipse(ax,ay,15,34,-.12,0,Math.PI*2);ctx.stroke();
    ctx.shadowBlur=0;ctx.shadowOffsetX=0;
    // Smooth pearlescent rim, with a broad cool reflection and a pink lower edge.
    ctx.strokeStyle='rgba(224,248,250,.72)';ctx.lineWidth=3;
    ctx.beginPath();ctx.ellipse(ax-2,ay,15,34,-.12,Math.PI*.5,Math.PI*1.5);ctx.stroke();
    ctx.strokeStyle='rgba(238,210,236,.62)';ctx.lineWidth=2.8;
    ctx.beginPath();ctx.ellipse(ax,ay+1,15,34,-.12,0,Math.PI*.6);ctx.stroke();
    ctx.strokeStyle='rgba(255,255,255,.98)';ctx.lineWidth=1.8;
    ctx.beginPath();ctx.ellipse(ax-1,ay-1,13,32,-.12,Math.PI*.9,Math.PI*1.75);ctx.stroke();
    ctx.restore();
  }
  drawSoapNeck(ctx, ax, ay, tipX, tipY, radius, progress, now){
    const len=Math.max(12,ax-tipX), pinch=1-Math.pow(progress,1.8);
    const waist=Math.max(.65,(11+3*Math.sin(now/340))*pinch);
    const mx=ax-len*.47, my=ay+(tipY-ay)*.47;
    const path=()=>{
      ctx.beginPath();ctx.moveTo(ax-2,ay-29);
      ctx.bezierCurveTo(ax-len*.20,ay-27,mx+len*.13,my-waist,mx,my-waist);
      ctx.bezierCurveTo(mx-len*.19,my-waist,tipX+len*.12,tipY-radius,tipX,tipY-radius);
      ctx.quadraticCurveTo(tipX-15,tipY,tipX,tipY+radius);
      ctx.bezierCurveTo(tipX+len*.12,tipY+radius,mx-len*.19,my+waist,mx,my+waist);
      ctx.bezierCurveTo(mx+len*.13,my+waist,ax-len*.20,ay+27,ax-2,ay+29);
      ctx.quadraticCurveTo(ax-10,ay,ax-2,ay-29);ctx.closePath();
    };
    ctx.save();ctx.globalAlpha=1-Math.pow(progress,8);path();
    const glass=ctx.createLinearGradient(0,ay-36,0,ay+36);
    glass.addColorStop(0,'rgba(151,183,218,.28)');glass.addColorStop(.15,'rgba(255,255,255,.48)');glass.addColorStop(.34,'rgba(81,140,145,.06)');glass.addColorStop(.65,'rgba(119,169,181,.09)');glass.addColorStop(.9,'rgba(248,204,227,.36)');glass.addColorStop(1,'rgba(255,255,255,.72)');
    ctx.fillStyle=glass;ctx.fill();
    ctx.strokeStyle='rgba(88,131,145,.30)';ctx.lineWidth=2.7;ctx.stroke();
    const rim=ctx.createLinearGradient(tipX,tipY-radius,ax,ay+29);
    for(const [k,col] of [[0,'#fffdf4'],[.16,'#e4b7e9'],[.32,'#82cfed'],[.48,'#c7edce'],[.64,'#fff0bd'],[.8,'#deb5e5'],[1,'#c5f4f5']])rim.addColorStop(k,col);
    ctx.strokeStyle=rim;ctx.lineWidth=1.6;ctx.stroke();
    path();ctx.clip();
    // Flowing interference bands stay on the wet film, never the vowel or its mapped color.
    for(let i=0;i<9;i++){
      const yy=ay-32+i*8+Math.sin(now/880+i)*4;
      ctx.beginPath();ctx.moveTo(tipX-10,yy);
      ctx.bezierCurveTo(mx-25,yy+Math.sin(i+now/950)*14,mx+20,yy-8,ax+8,yy+6);
      ctx.strokeStyle=['rgba(255,255,255,.37)','rgba(219,159,231,.22)','rgba(128,216,237,.27)','rgba(246,225,157,.22)'][i%4];
      ctx.lineWidth=i%3===0?2.8:1;ctx.stroke();
    }
    ctx.restore();
  }
  // 고리에 걸린 막. 목소리가 없을 때만 보인다 — 아직 방울이 되지 못한 막.
  drawWandFilm(ctx, ax, ay, now, e){
    // 3D 렌더 중이면 고리에 걸린 막을 GL 박막(무지갯빛 간섭)으로 그린다 — 고리 축에 맞춰 기울여서.
    if(this._glCap){ this.gl3d.film(e); return; }
    const R = 13*this.wandHeadScale, ry = 31*this.wandHeadScale, TAU = Math.PI*2;
    // 표면장력으로 아주 느리게 출렁인다
    const w = 1 + Math.sin(now/620)*0.03;
    ctx.save();
    ctx.globalAlpha = e;
    ctx.translate(ax,ay);ctx.rotate(this.wandAngle-.12);ctx.translate(-ax,-ay);
    ctx.beginPath(); ctx.ellipse(ax, ay, (R-1.5)*w, (ry-1.2)*w, 0, 0, TAU); ctx.clip();
    ctx.globalCompositeOperation = 'screen';
    // 흰 광량 + 오팔 한 겹 — 막이 빛을 머금고 있다
    const g = ctx.createRadialGradient(ax-R*0.3, ay-ry*0.3, 0, ax, ay, R);
    g.addColorStop(0,  'rgba(255,255,255,.40)');
    g.addColorStop(.6, 'rgba(255,255,255,.14)');
    g.addColorStop(1,  'rgba(255,255,255,.30)');
    ctx.fillStyle = g; ctx.fillRect(ax-R, ay-ry, R*2, ry*2);
    const th = now/2600;
    for(const [col, a, ox, oy, rad] of this.OPAL){
      const cs = Math.cos(th), sn = Math.sin(th);
      this.drawBloom(ctx, ax + R*(ox*cs - oy*sn)*0.8, ay + ry*(ox*sn + oy*cs)*0.8, R*rad*0.9, col, a*0.9);
    }
    ctx.restore();
  }
  // 군집의 아래 끝(중심 기준 오프셋). 방울은 이 끝이 고리에 닿도록 놓인다.
  clusterBottom(fake){
    const ps = this.layoutSegs(fake.segs);
    let bot = 0;
    fake.segs.forEach((s,i)=>{ bot = Math.max(bot, ps[i].y + s.r); });
    return bot;
  }

  drawForming(ctx, ax, ay, now){
    const c = this.cur;
    // 글자 각도는 프레임마다 '지금 음정의 회전 속도 × 경과 시간'을 더해 간다.
    // now×spin 으로 계산하면 음이 바뀌어 spin 이 조금만 변해도 now(수십만 ms)가 곱해져
    // 각도가 몇 바퀴씩 튀어, 음이 높을 때가 아니라 '음이 바뀔 때' 빨리 도는 것처럼 보였다.
    const fdt = Math.min(64, Math.max(0, now - (c._spinT || now))); c._spinT = now;
    for(const s of c.segs){
      if(s.fAcc === undefined) s.fAcc = (s.seed||0)*1.7;
      s.fAcc += this.pitchSpin(s.pitch)*fdt;
    }
    const segs = c.segs.map(s=>{
      const live = { v:s.v, r: this.segRadius(s.lvl), ar: this.aspect(s.pitch),
        alpha: this.segAlpha(((s.tEnd||now)-s.t0)/1000), ang: s.ang, olap: s.olap,
        sfx: s.sfx, ifx: s.ifx, seed: s.seed, tone: this.segTone(s.pitch), spin: this.pitchSpin(s.pitch), acc: s.fAcc };
      return live;
    });
    const fake = { segs, trem:c.trem, __owner:c };
    // ── 절대규칙: 방울은 돌지 않는다. 도는 것은 글자뿐이다. ─────────────
    // 군집 전체에 ctx.rotate 를 걸면 '음정 = 글자의 회전 속도'라는 자가 무너지고,
    // 비눗방울이 팽이처럼 보인다.
    // 떨림(비브라토) → 형성 중 버블의 너울. 진폭을 키워 발성 중에도 떨림이 눈에 보이게 한다.
    // 기본 4px 잔너울 + 떨림 흔들림(세로). 고리에 붙어 있어 떠다닐 때의 절반 폭만 준다.
    const tAmp = 4;
    const tw = this.tremWave(c, now, 0, 1, 0.5);
    const wobX = (Math.sin(now/300) + Math.sin(now/173)*0.4) * tAmp * 0.7;
    const wob  = (Math.sin(now/247 + 1.1) + Math.sin(now/181)*0.35) * tAmp + tw.y;
    const breath = 1 + Math.min(.03, this.smoothLvl*0.05)*Math.sin(now/520);
    // 군집의 바닥이 고리에 걸리도록 위로 올린다 — 방울은 고리에서 부풀어 나온다
    const pose=this.soapPose(fake,ax,ay,now-c.t0),port=this.soapPort(fake);
    // 연결점을 중심으로 부푸는 원래 방식 — 시작 비율을 덜 납작하게, 곡선은 S자로 부드럽게
    const tIn=Math.max(0,now-c.t0)/190, inflate=1-Math.exp(-tIn)*(1+tIn);

    ctx.save();ctx.translate(pose.x+wobX,pose.y+wob);
    // Inflate about the connection point, preserving the full mapped size after emergence.
    ctx.translate(port.x,port.y);ctx.scale(.26+.74*inflate,.42+.58*inflate);ctx.translate(-port.x,-port.y);
    ctx.save();
    ctx.scale(breath, breath);
    const sx=.26+.74*inflate,sy=.42+.58*inflate;
    this.drawPeanut(ctx,fake,now,{
      x:(port.x+(ax-pose.x-wobX-port.x)/sx)/breath,
      y:(port.y+(ay-pose.y-wob-port.y)/sy)/breath,
      ...this.wandFilmAxes(sx*breath,sy*breath),aperture:29*this.wandHeadScale/sy/breath,rimX:13*this.wandHeadScale/sx/breath,skew:3.5*this.wandHeadScale/sx/breath,progress:0
    });
    ctx.restore();
    // (방울 옆 음정 색상 게이지는 제거함 — 2026-09-30)
    ctx.restore();
  }

  killBubble(b, now){ b.dead = true; this.popBubble(b, now); }

  popBubble(b, now){
    b.gone = true;
    const R = Math.max(30, this.bubbleW(b)/2);
    // 막이 터지며 번지는 잔상 링 (렌더 전용 — 개수·속도 등 물리에는 관여하지 않음)
    if(this.gl3dOn()) this.gl3dPopOwner(b);
    else this.parts.push({x:b.x, y:b.y, vx:0, vy:0, r:R*.55, a:1, a0:0, ring:true, c:''});
    const letterless = !b.segs.some(s=>s.v);
    if(this.gl3dOn()){ /* 물방울은 3D 층이 뿌린다 */ }
    else if(letterless){
      // 이름 없는 버블은 귀엽게 통통 터짐: 동글동글한 방울 파편이 통통 튐
      for(let i=0;i<10;i++) this.parts.push({x:b.x+(Math.random()-.5)*R, y:b.y+(Math.random()-.5)*R, vx:(Math.random()-.5)*2, vy:-(1+Math.random()*2), r:2+Math.random()*3, a:1, a0:0, dot:true, c:'rgba(18,165,143,.68)'});
    } else {
      for(let i=0;i<14;i++) this.parts.push({x:b.x+(Math.random()-.5)*R, y:b.y+(Math.random()-.5)*R, vx:(Math.random()-.5)*3, vy:(Math.random()-.5)*3, r:2+Math.random()*5, a:1, a0:Math.random()*6, c: Math.random()<.5?'rgba(18,165,143,.72)':'rgba(255,111,156,.75)'});
    }
    const vset = new Set(b.segs.filter(s=>s.v).map(s=>s.v));
    if(vset.size===1){
      const v=[...vset][0];
      this.ghosts.push({v, x:b.x, y:b.y, a:1, size: Math.max(20, b.segs[0].r*.7)});
    }
  }

  collide(now){
    const bs = this.bubbles;
    for(let i=0;i<bs.length;i++) for(let j=i+1;j<bs.length;j++){
      const a=bs[i], b=bs[j];
      if(a.gone||b.gone||a.rising||b.rising||a.dead||b.dead||a.blown||b.blown) continue;
      const ra=this.bubbleW(a)/2, rb=this.bubbleW(b)/2;
      const dx=b.x-a.x, dy=b.y-a.y, d=Math.hypot(dx,dy);
      if(d > (ra+rb)*.95 || d===0) continue;
      // 충돌하면 서로 밀려나기만 한다 — 각 발성으로 만든 형태가 합쳐지거나 사라지지 않도록.
      // (예전의 같은 모음 결합·다른 모음 대결 터짐은 제거)
      const nx=dx/d, ny=dy/d;
      const push = ((ra+rb)*.95 - d)/2;          // 겹친 만큼 양쪽으로 떼어 놓아 다시 붙지 않게
      a.x -= nx*push; a.y -= ny*push; b.x += nx*push; b.y += ny*push;
      a.vx = -nx*(2+Math.random()); a.vy = -ny*(1.5+Math.random()); a.tvx=a.vx; a.tvy=a.vy; a.wt=now+1400;
      b.vx = nx*(2+Math.random()); b.vy = ny*(1.5+Math.random()); b.tvx=b.vx; b.tvy=b.vy; b.wt=now+1400;
    }
  }

  drawGraph(now, targetCanvas){
    const gc = targetCanvas || this.graphRef.current; if(!gc) return;
    const ctx = gc.getContext('2d'), W = gc.width, H = gc.height;
    // 해상도를 올려도(캡처용 고배율 캔버스 포함) 선 굵기·점 크기가 원래 비율 그대로 보이도록
    // 기준 해상도(112px 높이) 대비 배율 k 로 절대 픽셀 값들을 함께 키운다.
    const k = H/112;
    ctx.clearRect(0,0,W,H);
    ctx.fillStyle = 'rgba(18,63,57,.05)'; ctx.fillRect(0,0,W,H);
    ctx.strokeStyle = 'rgba(18,63,57,.16)'; ctx.lineWidth = k;
    ctx.beginPath(); ctx.moveTo(0,H-k); ctx.lineTo(W,H-k); ctx.stroke();
    const span = 3200;
    const pad = 8*k;
    // 세기 파형 (시안 영역)
    ctx.beginPath(); ctx.moveTo(0,H);
    for(const w of this.wave){
      const x = (1-(now-w.t)/span)*W;
      ctx.lineTo(x, H - w.lvl*(H-pad));
    }
    ctx.lineTo(W,H); ctx.closePath();
    const gg2 = ctx.createLinearGradient(0,0,0,H);
    gg2.addColorStop(0,'rgba(18,165,143,.42)'); gg2.addColorStop(1,'rgba(18,165,143,.10)');
    ctx.fillStyle = gg2; ctx.fill();
    // 피치 점은 뺐다 — 세기(곡선)와 피치(점)는 서로 다른 값이라 겹쳐 그리면
    // 범례 없이는 헷갈린다. 필요하면 이 블록을 되살리면 된다.
    // 임계값 라인
    const ty = H - this.state.thresh*(H-pad);
    ctx.strokeStyle = 'rgba(18,63,57,.28)'; ctx.lineWidth = k; ctx.setLineDash([3*k,4*k]);
    ctx.beginPath(); ctx.moveTo(0,ty); ctx.lineTo(W,ty); ctx.stroke();
    ctx.setLineDash([]);
  }

  // 떨림 → 방울 흔들림. 억양 흔들림(느림)은 넓고 느린 사인, 잔떨림(빠름)은 좁고 빠른 사인.
  // (nx, ny) 방향으로만 흔든다 — 진행 방향에 수직으로 주면 지나간 자리가 사인 그래프처럼 보인다.
  // 위상은 경과 시간으로 적분하므로 빠르기가 바뀌어도 튀지 않는다. 저역통과를 거치지 않는다.
  tremWave(o, now, nx, ny, k=1){
    const dt = Math.min(64, Math.max(0, now - (o._tT || now))); o._tT = now;
    const S = Math.max(0, Math.min(1, o.tremS || 0)), F = Math.max(0, Math.min(1, o.tremF || 0));
    const fS = Math.max(0.6, Math.min(2, o.tremSHz || 1));
    const fF = Math.max(3, Math.min(this.TREM_FAST_VIS_HZ_MAX, o.tremFHz || 6));
    o._phS = (o._phS || 0) + 2*Math.PI*fS*dt/1000;
    o._phF = (o._phF || 0) + 2*Math.PI*fF*dt/1000;
    const d = (Math.sin(o._phS)*S*this.TREM_SLOW_PX + Math.sin(o._phF)*F*this.TREM_FAST_PX)*k;
    return {x: nx*d, y: ny*d};
  }

  // 음높이 그래프: 세기 그래프와 같은 3.2초 창. 세로축은 기준음(pitchCenter) 대비 반음,
  // 가운데 점선이 기준음이고 위아래로 PITCH_GRAPH_ST 반음까지 보인다. 발성 중인 f0 만 선으로 잇는다.
  PITCH_GRAPH_ST = 7;
  drawPitchGraph(now, targetCanvas){
    const gc = targetCanvas || this.pitchGraphRef.current; if(!gc) return;
    const ctx = gc.getContext('2d'), W = gc.width, H = gc.height;
    const k = H/112;
    ctx.clearRect(0,0,W,H);
    ctx.fillStyle = 'rgba(18,63,57,.05)'; ctx.fillRect(0,0,W,H);
    const span = 3200, pad = 8*k, mid = H/2, half = H/2 - pad;
    // 기준음 점선
    ctx.strokeStyle = 'rgba(18,63,57,.28)'; ctx.lineWidth = k; ctx.setLineDash([3*k,4*k]);
    ctx.beginPath(); ctx.moveTo(0,mid); ctx.lineTo(W,mid); ctx.stroke();
    ctx.setLineDash([]);
    const center = this.pitchCenter(), R = this.PITCH_GRAPH_ST;
    ctx.strokeStyle = 'rgba(18,125,110,.85)'; ctx.lineWidth = 2.2*k; ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.beginPath();
    let pen = false, lastT = 0;
    for(const w of this.wave){
      if(!(w.p > 0) || !w.v){ pen = false; continue; }
      const st = Math.max(-R, Math.min(R, 12*Math.log2(w.p/center)));
      const x = (1-(now-w.t)/span)*W, y = mid - (st/R)*half;
      if(pen && w.t - lastT < 120) ctx.lineTo(x, y); else ctx.moveTo(x, y);
      pen = true; lastT = w.t;
    }
    ctx.stroke();
    ctx.fillStyle = 'rgba(18,63,57,.45)'; ctx.font = '600 '+(9*k)+'px '+this.UIFONT; ctx.textAlign = 'left';
    ctx.fillText('음높이', 5*k, 11*k);
  }

  // 논문용: 화면에 보이는 작은 그래프(452x112)를 그대로 캡처하면 화질이 깨지므로,
  // 같은 그리기 로직을 훨씬 큰 오프스크린 캔버스에 다시 그려 고해상도 PNG로 내려받는다.
  exportGraphPNG = (scale=4)=>{
    // toBlob 은 비동기라 콜백이 실행될 때쯤 '클릭으로 인정되는 시간'이 지나
    // 크롬이 다운로드를 조용히 막는 경우가 있다. toDataURL 은 동기라 그 문제가 없다.
    try{
      const src = this.graphRef.current; if(!src) return;
      const cap = document.createElement('canvas');
      cap.width = src.width*scale; cap.height = src.height*scale;
      this.drawGraph(performance.now(), cap);
      const url = cap.toDataURL('image/png');
      const a = document.createElement('a');
      a.href = url; a.download = `sorijit_graph_${Date.now()}.png`;
      document.body.appendChild(a); a.click(); document.body.removeChild(a);
    }catch(err){
      console.error('그래프 PNG 저장 실패:', err);
      alert('그래프 저장에 실패했어요: ' + err.message);
    }
  };

  calibrateNoise = ()=>{
    if(!this.state.running || this.state.calibrating) return;
    this.calibMax = 0; this.calibEnd = performance.now()+1600;
    this.setState({calibrating:true, recogRefF0:null});
    // 서버 캘리브레이션도 같은 발화 구간에서 시작 — 끝은 위 loop() 의 calibEnd 분기에서 보낸다.
    if(this.ws && this.ws.readyState === WebSocket.OPEN) this.ws.send(JSON.stringify({type:'calibrate_start'}));
  };

  renderVals(){
    const s = this.state;
    const bar = (v,c)=>`position:absolute;left:0;top:0;bottom:0;width:${Math.round(Math.min(1,v)*100)}%;background:${c}`;
    return {
      canvasRef: this.canvasRef, graphRef: this.graphRef, pitchGraphRef: this.pitchGraphRef,
      notRunning: !s.running, start: this.start, startDemo: this.startDemo, errMsg: s.err,
      showMeters: s.meters && s.running,
      showGraph: s.graph,
      metersOn: s.meters, metersOff: !s.meters, graphOn: s.graph, graphOff: !s.graph,
      toggleMeters: ()=>this.setState(p=>({meters:!p.meters})),
      toggleGraph: ()=>this.setState(p=>({graph:!p.graph})),
      freezeOn: s.freeze, freezeOff: !s.freeze,
      toggleFreeze: ()=>this.setState(p=>({freeze:!p.freeze})),
      resetBubbles: ()=>{ this.bubbles=[]; this.ghosts=[]; this.parts=[]; this.remnants=[]; },
      voicedNow: s.voiced,
      vowelLabel: s.vowel || '–',
      levelBarStyle: bar(s.level,'var(--color-accent)'),
      pitchTrackStyle: 'height:7px;border-radius:999px;position:relative;overflow:hidden;background:var(--color-neutral-200);opacity:' + (s.pitch ? 1 : .35),
      pitchBarStyle: s.pitch
        ? 'position:absolute;top:-1px;bottom:-1px;width:3px;border-radius:2px;background:#fff;box-shadow:0 0 0 1px rgba(18,63,57,.35);left:calc(' + Math.round((this.pitchTone(s.pitch)+1)/2*100) + '% - 1.5px)'
        : 'display:none',
      durBarStyle: bar(s.dur/this.OPACITY_FULL_S,'var(--color-neutral-600)'),
      tremBarStyle: bar(s.trem,'var(--color-neutral-600)'),
      levelPct: Math.round(s.level*100)+'%',
      pitchHz: s.pitch?s.pitch+' Hz':'–',
      durSec: s.dur?s.dur.toFixed(1)+' s':'–',
      tremVal: s.trem?s.trem.toFixed(2):'–',
      menuOpen: s.menuOpen, toggleMenu: ()=>this.setState(p=>({menuOpen:!p.menuOpen})),
      sens: s.sens, sensLabel: '×'+s.sens.toFixed(1),
      thresh: s.thresh, threshLabel: s.thresh.toFixed(3),
      basePitch: s.basePitch, basePitchLabel: s.basePitch+' Hz',
      endHold: s.endHold, endHoldLabel: (s.endHold/1000).toFixed(2)+' s',
      sizeMul: s.sizeMul, sizeMulLabel: '×'+s.sizeMul.toFixed(1),
      vowelTol: s.vowelTol, vowelTolLabel: s.vowelTol<=0.45?'엄격':s.vowelTol>=0.85?'관대':'보통',
      setEndHold: e=>this.setState({endHold:+e.target.value}),
      setSizeMul: e=>this.setState({sizeMul:+e.target.value}),
      setVowelTol: e=>this.setState({vowelTol:+e.target.value}),
      presetMale: ()=>{ this.pitchAvg = 130; this.setState({basePitch:130}); },
      presetFemale: ()=>{ this.pitchAvg = 210; this.setState({basePitch:210}); },
      presetChild: ()=>{ this.pitchAvg = 260; this.setState({basePitch:260}); },
      setSens: e=>this.setState({sens:+e.target.value}),
      setThresh: e=>this.setState({thresh:+e.target.value}),
      setBasePitch: e=>{ this.pitchAvg = +e.target.value; this.setState({basePitch:+e.target.value}); },
      calibrateNoise: this.calibrateNoise,
      bgDepth: s.bgDepth,
      bgDepthLabel: Math.round(s.bgDepth*100)+'%',
      setBgDepth: e=>this.setState({bgDepth:+e.target.value}),
      bgShift: s.bgShift,
      bgShiftLabel: s.bgShift < 0.03 ? '같은 색' : Math.round(s.bgShift*100)+'%',
      setBgShift: e=>this.setState({bgShift:+e.target.value}),
      bgSoft: s.bgMode==='soft', bgVivid: s.bgMode==='vivid', bgOff: s.bgMode==='off',
      setBgSoft: ()=>this.setState({bgMode:'soft'}),
      setBgVivid: ()=>this.setState({bgMode:'vivid'}),
      setBgOff: ()=>this.setState({bgMode:'off'}),
      calBtnLabel: s.calibrating ? '주변 소음 측정 중…' : '주변 소음 자동 측정',
      recogRefF0Label: s.recogRefF0 ? `서버 기준 피치 ${Math.round(s.recogRefF0)} Hz` : '',
      srWarnMsg: s.srWarn,
      r3dOn: s.render3d && s.gl3dStatus==='ready', r3dOff: !(s.render3d && s.gl3dStatus==='ready'),
      setR3d: ()=>{ if(this.gl3d) this.setState({render3d:true}); },
      setR2d: ()=>this.setState({render3d:false}),
      recogWSOn: s.useRecogWS, recogWSOff: !s.useRecogWS,
      setRecogWS: ()=>this.setState({useRecogWS:true}, ()=>this.connectRecogWS()),
      setRecogFormant: ()=>this.setState({useRecogWS:false}, ()=>this.disconnectRecogWS()),
      recogStatusLabel: ({off:'꺼짐', connecting:'연결 중…', live:'연결됨', lost:'서버 대기 중 · 포먼트로 대체'})[s.recogStatus] || s.recogStatus,
      recogLive: s.recogStatus==='live',
      r3dMsg: s.gl3dStatus==='loading' ? '3D 렌더를 불러오는 중' : s.gl3dStatus==='failed' ? '이 브라우저에서 WebGL을 쓸 수 없어 2D로 그립니다' : '',
    };
  }

  // ── 화면 ──────────────────────────────────────────────────────────────
  // 원본 프로토타입 템플릿(x-dc)을 JSX 로 옮긴 것. v = props 기본값 + props + renderVals().
  render(){
    const v = { ...DEFAULT_PROPS, ...this.props, ...(this.renderVals() || {}) };
    return (
      <div className="sc-root">
        <div className="bubble-app" style={{position:"fixed",inset:"0",fontFamily:"var(--font-body)",background:
  "radial-gradient(ellipse 82% 56% at 44% -2%, rgba(255,255,255,.07) 0%, rgba(255,255,255,0) 76%)," +
  "#000"}} data-screen-label="버블 발성 캔버스">
          <canvas ref={v.canvasRef} style={{position:"absolute",inset:"0",width:"100%",height:"100%",display:"block"}} />
          <div className="app-heading" style={{position:"absolute",top:"30px",left:"44px",pointerEvents:"none",zIndex:"3"}}>
            <h1 className="sorijit-wordmark" style={{margin:"0"}}>
              소리짓
            </h1>
          </div>
          <div className="app-settings" style={{position:"absolute",top:"28px",right:"40px",zIndex:"5",display:"flex",flexDirection:"column",alignItems:"flex-end",gap:"10px"}}>
            <button className="btn btn-icon glass" onClick={v.toggleMenu} aria-label="캘리브레이션" style={{display:"flex",flexDirection:"column",justifyContent:"center",alignItems:"center",gap:"4px",width:"44px",height:"44px",color:"var(--color-accent-700)",borderRadius:"999px"}}>
              <span style={{display:"block",width:"17px",height:"2.2px",borderRadius:"2px",background:"currentColor"}} />
              <span style={{display:"block",width:"17px",height:"2.2px",borderRadius:"2px",background:"currentColor"}} />
              <span style={{display:"block",width:"17px",height:"2.2px",borderRadius:"2px",background:"currentColor"}} />
            </button>
            {v.menuOpen ? (
              <>
                <div className="glass panel-scroll" style={{width:"292px",padding:"20px 22px 22px",maxHeight:"calc(100vh - 108px)",overflowY:"auto",overscrollBehavior:"contain"}}>
                  <div style={{fontFamily:"var(--font-heading)",fontSize:"13.5px",fontWeight:"700",letterSpacing:".01em",color:"var(--color-text)",marginBottom:"16px"}}>
                    캘리브레이션 · 기본
                  </div>
                  <div style={{display:"flex",flexDirection:"column",gap:"14px",fontSize:"13px",color:"var(--color-text)"}}>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                        음역 프리셋
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        <button className="btn btn-secondary" onClick={v.presetMale} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          성인 남성
                        </button>
                        <button className="btn btn-secondary" onClick={v.presetFemale} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          성인 여성
                        </button>
                        <button className="btn btn-secondary" onClick={v.presetChild} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          아동
                        </button>
                      </div>
                    </div>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          마이크 감도
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.sensLabel}
                        </span>
                      </span>
                      <input type="range" min="0.4" max="3" step="0.1" value={v.sens} onChange={v.setSens} />
                    </label>
                    <button className="btn btn-secondary" onClick={v.calibrateNoise} style={{width:"100%"}}>
                      {v.calBtnLabel}
                    </button>
                    {v.recogRefF0Label ? (
                      <span style={{fontSize:"11.5px",color:"var(--color-neutral-500)"}}>
                        {v.recogRefF0Label}
                      </span>
                    ) : null}
                    <div style={{fontFamily:"var(--font-heading)",fontSize:"13.5px",fontWeight:"700",letterSpacing:".01em",color:"var(--color-text)",margin:"8px 0 2px",borderTop:"1px solid var(--color-divider)",paddingTop:"14px"}}>
                      고급
                    </div>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          인식 소스
                        </span>
                        <span style={{fontSize:"11.5px",fontWeight:"600",color: v.recogLive ? "var(--color-accent-700)" : "var(--color-neutral-500)"}}>
                          {v.recogStatusLabel}
                        </span>
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        <button className={v.recogWSOn ? "btn btn-primary" : "btn btn-secondary"} onClick={v.setRecogWS} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          Python 모델
                        </button>
                        <button className={v.recogWSOff ? "btn btn-primary" : "btn btn-secondary"} onClick={v.setRecogFormant} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          브라우저 포먼트
                        </button>
                      </div>
                      <span style={{fontSize:"11.5px",color:"var(--color-neutral-500)",lineHeight:"1.5"}}>
                        Python 모델은 remark_ws_server2.py 실행이 필요합니다 (ws://localhost:8765). 연결 전이거나 끊기면 자동으로 포먼트 분석으로 대체됩니다.
                      </span>
                      {v.srWarnMsg ? (
                        <span style={{fontSize:"11.5px",color:"var(--color-accent-2-700)",lineHeight:"1.5"}}>
                          {v.srWarnMsg}
                        </span>
                      ) : null}
                    </div>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          발성 감지 임계값
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.threshLabel}
                        </span>
                      </span>
                      <input type="range" min="0.02" max="0.2" step="0.005" value={v.thresh} onChange={v.setThresh} />
                    </label>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          기준 피치 (음역대)
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.basePitchLabel}
                        </span>
                      </span>
                      <input type="range" min="120" max="300" step="5" value={v.basePitch} onChange={v.setBasePitch} />
                    </label>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          발성 종료 판정 시간
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.endHoldLabel}
                        </span>
                      </span>
                      <input type="range" min="200" max="1000" step="20" value={v.endHold} onChange={v.setEndHold} />
                    </label>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          버블 크기 배율
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.sizeMulLabel}
                        </span>
                      </span>
                      <input type="range" min="0.5" max="2" step="0.1" value={v.sizeMul} onChange={v.setSizeMul} />
                    </label>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                        화면 표시
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        {v.metersOn ? (
                          <>
                            <button className="btn btn-primary" onClick={v.toggleMeters} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              발성 지표 켬
                            </button>
                          </>
                        ) : null}
                        {v.metersOff ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.toggleMeters} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              발성 지표 끔
                            </button>
                          </>
                        ) : null}
                        {v.graphOn ? (
                          <>
                            <button className="btn btn-primary" onClick={v.toggleGraph} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              그래프 켬
                            </button>
                          </>
                        ) : null}
                        {v.graphOff ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.toggleGraph} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              그래프 끔
                            </button>
                          </>
                        ) : null}
                      </div>
                    </div>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                        캡처 모드 (버블 고정·드래그 배치)
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        {v.freezeOn ? (
                          <>
                            <button className="btn btn-primary" onClick={v.toggleFreeze} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              고정 켬
                            </button>
                          </>
                        ) : null}
                        {v.freezeOff ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.toggleFreeze} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              고정 끔
                            </button>
                          </>
                        ) : null}
                        <button className="btn btn-secondary" onClick={v.resetBubbles} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                          리셋
                        </button>
                      </div>
                      {v.freezeOn ? (
                        <span style={{color:"var(--color-neutral-500)",fontSize:"11.5px"}}>
                          고정 중에는 버블이 멈추고, 마우스로 드래그해 위치를 옮길 수 있어요.
                        </span>
                      ) : null}
                    </div>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                        방울 렌더
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        {v.r3dOn ? (
                          <>
                            <button className="btn btn-primary" style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              3D 실사
                            </button>
                            <button className="btn btn-secondary" onClick={v.setR2d} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              2D 일러스트
                            </button>
                          </>
                        ) : null}
                        {v.r3dOff ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.setR3d} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              3D 실사
                            </button>
                            <button className="btn btn-primary" style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              2D 일러스트
                            </button>
                          </>
                        ) : null}
                      </div>
                      {v.r3dMsg ? (
                        <>
                          <span style={{fontSize:"11.5px",color:"var(--color-neutral-500)"}}>
                            {v.r3dMsg}
                          </span>
                        </>
                      ) : null}
                    </div>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          배경 진하기
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.bgDepthLabel}
                        </span>
                      </span>
                      <input type="range" min="0" max="1" step="0.01" value={v.bgDepth} onChange={v.setBgDepth} />
                    </label>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          배경–버블 대비
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.bgShiftLabel}
                        </span>
                      </span>
                      <input type="range" min="0" max="1" step="0.01" value={v.bgShift} onChange={v.setBgShift} />
                    </label>
                    <div style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                        배경 색 (음정 반응)
                      </span>
                      <div style={{display:"flex",gap:"6px"}}>
                        {v.bgSoft ? (
                          <>
                            <button className="btn btn-primary" style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              은은
                            </button>
                            <button className="btn btn-secondary" onClick={v.setBgVivid} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              뚜렷
                            </button>
                            <button className="btn btn-secondary" onClick={v.setBgOff} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              끔
                            </button>
                          </>
                        ) : null}
                        {v.bgVivid ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.setBgSoft} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              은은
                            </button>
                            <button className="btn btn-primary" style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              뚜렷
                            </button>
                            <button className="btn btn-secondary" onClick={v.setBgOff} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              끔
                            </button>
                          </>
                        ) : null}
                        {v.bgOff ? (
                          <>
                            <button className="btn btn-secondary" onClick={v.setBgSoft} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              은은
                            </button>
                            <button className="btn btn-secondary" onClick={v.setBgVivid} style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              뚜렷
                            </button>
                            <button className="btn btn-primary" style={{flex:"1",padding:"6px 0",fontSize:"12.5px"}}>
                              끔
                            </button>
                          </>
                        ) : null}
                      </div>
                    </div>
                    <label style={{display:"flex",flexDirection:"column",gap:"6px"}}>
                      <span style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                          모음 인식 민감도
                        </span>
                        <span style={{fontVariantNumeric:"tabular-nums"}}>
                          {v.vowelTolLabel}
                        </span>
                      </span>
                      <input type="range" min="0.3" max="1.2" step="0.05" value={v.vowelTol} onChange={v.setVowelTol} />
                    </label>
                    <p style={{margin:"0",fontSize:"11.5px",lineHeight:"1.5",color:"var(--color-neutral-500)"}}>
                      주변이 조용한 상태에서 소음 측정을 누르면 임계값이 자동 조정됩니다. 음정은 도는 속도로 나타납니다 — 높은 음일수록 빨리, 낮은 음일수록 천천히. 색은 가시광선 파장을 그대로 씁니다 — 기준음보다 낮으면 파랑·보라(400nm) 쪽, 기준음이면 연두(540nm), 높으면 주황·빨강(680nm) 쪽. 화면에는 한 순간에 한 파장만 나타납니다. 배경은 방울과 언제나 같은 파장을 쓰되 '배경–버블 대비'만큼 더 옅게 흐릅니다 — 톤은 어긋날 수 없고, 지금 만들어지는 방울만 앞으로 나옵니다. 대비를 0으로 두면 배경과 방울이 같은 색이 됩니다. 기준음은 발성이 쌓이면 화자의 음역 중심으로 천천히 옮겨 가므로, 목소리가 높든 낮든 스펙트럼 양쪽을 다 쓰게 됩니다. 떠오른 방울은 발화 당시의 색을 테두리에 지닌 채, 회전이 점점 느려지다 멎는 순간 터집니다. 떨림이 클수록 울렁임의 폭이 넓어집니다. 인식 민감도를 관대하게 두면 인식불가가 줄어듭니다.
                    </p>
                  </div>
                </div>
              </>
            ) : null}
          </div>
          {v.showMeters ? (
            <>
              <div className="glass app-meters" style={{position:"absolute",left:"44px",bottom:"36px",width:"262px",padding:"16px 18px 18px",pointerEvents:"none",zIndex:"3"}}>
                <div style={{fontFamily:"var(--font-heading)",fontSize:"12.5px",fontWeight:"700",letterSpacing:".01em",color:"var(--color-text)",borderBottom:"1px solid var(--color-divider)",paddingBottom:"8px",marginBottom:"12px",display:"flex",justifyContent:"space-between",alignItems:"center"}}>
                  <span style={{display:"flex",alignItems:"center",gap:"6px"}}>
                    실시간 발성 지표
                    {v.recogLive ? (<span style={{fontSize:"10px",fontWeight:"600",color:"var(--color-accent-700)",padding:"1px 6px",borderRadius:"999px",background:"rgba(18,165,143,.14)"}}>Python</span>) : null}
                  </span>
                  {v.voicedNow ? (
                    <>
                      <span style={{width:"8px",height:"8px",borderRadius:"50%",background:"var(--color-accent-2)",animation:"pulseDot 1s infinite"}} />
                    </>
                  ) : null}
                </div>
                {v.showGraph ? (
                  <>
                    <canvas ref={v.graphRef} width="1808" height="448" style={{width:"226px",height:"56px",display:"block",marginBottom:"6px",borderRadius:"12px",pointerEvents:"auto"}} />
                    <canvas ref={v.pitchGraphRef} width="1808" height="448" style={{width:"226px",height:"56px",display:"block",marginBottom:"12px",borderRadius:"12px",pointerEvents:"auto"}} />
                  </>
                ) : null}
                <div style={{display:"grid",gridTemplateColumns:"50px 1fr 56px",gap:"7px 10px",alignItems:"center",fontSize:"12.5px",color:"var(--color-text)"}}>
                  <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                    모음
                  </span>
                  <span style={{fontFamily:"var(--font-heading)",fontSize:"23px",fontWeight:"700",lineHeight:"1",color:"var(--color-accent-700)"}}>
                    {v.vowelLabel}
                  </span>
                  <span />
                  <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                    세기
                  </span>
                  <span style={{height:"7px",borderRadius:"999px",background:"var(--color-neutral-200)",position:"relative",overflow:"hidden"}}>
                    <span style={cssObj(v.levelBarStyle)} />
                  </span>
                  <span style={{textAlign:"right",fontVariantNumeric:"tabular-nums"}}>
                    {v.levelPct}
                  </span>
                  <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                    피치
                  </span>
                  <span style={cssObj(v.pitchTrackStyle)}>
                    <span style={cssObj(v.pitchBarStyle)} />
                  </span>
                  <span style={{textAlign:"right",fontVariantNumeric:"tabular-nums"}}>
                    {v.pitchHz}
                  </span>
                  <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                    길이
                  </span>
                  <span style={{height:"7px",borderRadius:"999px",background:"var(--color-neutral-200)",position:"relative",overflow:"hidden"}}>
                    <span style={cssObj(v.durBarStyle)} />
                  </span>
                  <span style={{textAlign:"right",fontVariantNumeric:"tabular-nums"}}>
                    {v.durSec}
                  </span>
                  <span style={{color:"var(--color-neutral-600)",fontWeight:"500"}}>
                    떨림
                  </span>
                  <span style={{height:"7px",borderRadius:"999px",background:"var(--color-neutral-200)",position:"relative",overflow:"hidden"}}>
                    <span style={cssObj(v.tremBarStyle)} />
                  </span>
                  <span style={{textAlign:"right",fontVariantNumeric:"tabular-nums"}}>
                    {v.tremVal}
                  </span>
                </div>
              </div>
            </>
          ) : null}
          {v.notRunning ? (
            <>
              <div className="welcome" style={{position:"absolute",inset:"0",zIndex:"10",display:"flex",alignItems:"center",justifyContent:"center",background:"rgba(238,248,243,.62)",WebkitBackdropFilter:"blur(16px) saturate(140%)",backdropFilter:"blur(16px) saturate(140%)"}}>
                <div style={{textAlign:"center",maxWidth:"560px",padding:"0 24px",display:"flex",flexDirection:"column",alignItems:"center"}}>
                  <div className="sj-logo" aria-label="소리짓">
                    <span className="sj-logo-stroke" aria-hidden="true">
                      소리짓
                    </span>
                    <h1 className="sj-logo-fill">
                      소리짓
                    </h1>
                  </div>
                  <svg className="sj-hero" viewBox="0 0 360 220" width="360" height="220" aria-hidden="true">
                    <defs>
                      <linearGradient id="sjBody" x1="0" y1="0" x2="1" y2="1">
                        <stop offset="0" stopColor="#3f8c86" />
                        <stop offset="1" stopColor="#6a5b8e" />
                      </linearGradient>
                      <linearGradient id="sjBub" x1="0" y1="0" x2="1" y2="1">
                        <stop offset="0" stopColor="#7fd3c6" stopOpacity=".55" />
                        <stop offset=".55" stopColor="#b9a6dc" stopOpacity=".35" />
                        <stop offset="1" stopColor="#7f9fd6" stopOpacity=".5" />
                      </linearGradient>
                      <radialGradient id="sjHi" cx=".32" cy=".3" r=".5">
                        <stop offset="0" stopColor="#fff" stopOpacity=".95" />
                        <stop offset="1" stopColor="#fff" stopOpacity="0" />
                      </radialGradient>
                    </defs>
                    <g fill="url(#sjBody)">
                      <path d="M60 220 C60 168 78 146 104 140 L104 118 C86 108 78 88 84 66 C90 44 112 34 130 40 C150 46 158 66 154 86 C151 100 142 110 132 116 L132 140 C158 146 176 168 176 220 Z" />
                      <path d="M92 44 C98 26 124 20 142 32 C150 38 152 48 148 54 C138 40 116 38 98 52 Z" />
                      <circle cx="82" cy="48" r="14" />
                      <path d="M124 160 C150 150 186 132 218 118 L226 132 C196 146 172 166 150 190 C138 196 124 184 124 160 Z" />
                      <circle cx="223" cy="124" r="9" />
                    </g>
                    <circle cx="146" cy="92" r="9" fill="#5a8c95" opacity=".55" />
                    <circle cx="146" cy="92" r="9" fill="url(#sjHi)" opacity=".5" />
                    <path d="M228 118 L268 84" stroke="#2b5f60" strokeWidth="4" strokeLinecap="round" />
                    <ellipse cx="276" cy="76" rx="9" ry="14" transform="rotate(-38 276 76)" fill="none" stroke="#2b5f60" strokeWidth="3.5" />
                    <ellipse cx="276" cy="76" rx="7" ry="11" transform="rotate(-38 276 76)" fill="url(#sjBub)" />
                    <path d="M158 92 C176 88 196 84 218 82" stroke="#7fb3b8" strokeWidth="2" strokeLinecap="round" strokeDasharray="3 6" fill="none" opacity=".7" />
                    <g>
                      <circle cx="300" cy="56" r="13" fill="url(#sjBub)" stroke="#fff" strokeWidth="1.6" />
                      <circle cx="300" cy="56" r="13" fill="url(#sjHi)" opacity=".8" />
                      <circle cx="322" cy="30" r="20" fill="url(#sjBub)" stroke="#fff" strokeWidth="1.6" />
                      <circle cx="322" cy="30" r="20" fill="url(#sjHi)" opacity=".8" />
                      <circle cx="286" cy="22" r="8" fill="url(#sjBub)" stroke="#fff" strokeWidth="1.4" />
                      <circle cx="286" cy="22" r="8" fill="url(#sjHi)" opacity=".8" />
                      <circle cx="252" cy="40" r="5" fill="url(#sjBub)" stroke="#fff" strokeWidth="1.2" />
                      <circle cx="332" cy="72" r="6" fill="url(#sjBub)" stroke="#fff" strokeWidth="1.2" />
                    </g>
                  </svg>
                  <div style={{display:"flex",gap:"12px",justifyContent:"center"}}>
                    <button className="btn btn-primary" onClick={v.start} style={{fontSize:"15.5px",padding:"12px 28px"}}>
                      마이크 켜고 시작
                    </button>
                    <button className="btn btn-secondary" onClick={v.startDemo} style={{fontSize:"15.5px",padding:"12px 28px"}}>
                      마이크 없이 데모 보기
                    </button>
                  </div>
                  {v.errMsg ? (
                    <>
                      <p style={{marginTop:"16px",fontSize:"13px",color:"var(--color-accent-2-700)"}}>
                        {v.errMsg}
                      </p>
                    </>
                  ) : null}
                </div>
              </div>
            </>
          ) : null}
        </div>
      </div>
    );
  }
}

