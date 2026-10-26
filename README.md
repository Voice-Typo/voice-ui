# 소리짓 — React(JSX) 버전

원본 단일 HTML 프로토타입을 React 컴포넌트로 옮긴 것입니다.

## 실행
```
npm install
npm run dev        # http://localhost:5173
npm run build      # dist/ 에 정적 빌드
```
Node 18 이상, 브라우저는 WebGL2 지원(Chrome/Edge/Safari 최신).

## 구조
- `src/SoriJit.jsx` — 앱 전체. 음성 분석·방울 물리·매핑·2D 렌더러·화면(JSX)이 한 파일에 있습니다.
  다른 React 프로젝트에 넣을 땐 이 파일과 `src/sorijit.css`, `public/assets/` 를 함께 옮기면 됩니다.
  `<SoriJit genZone={0.78} showMeters showGraph />` 처럼 씁니다(props 생략 시 기본값).
- `src/sorijit.css` — 디자인 시스템 토큰과 스타일.
- `public/assets/` — 3D 렌더 모듈(three.js 번들, `58bef27f…js`), 환경맵(`06d1c89e…jpg`), 막대 3D 모델(`532bbe92…glb`), 폰트.
  `/assets/…` 경로로 불러오므로 프로젝트 루트에서 서빙되어야 합니다. 경로를 바꾸려면 `SoriJit.jsx` 의 `RES` 상수와 `sorijit.css` 의 `url(...)` 을 같이 바꾸세요.

## 원본과 다른 점
- 템플릿의 `sc-if` → `{cond ? … : null}`, `{{ x }}` → `{v.x}`, `sc-camel-on-input` → `onChange` 로 기계 변환했습니다.
- 인라인 스타일 문자열은 객체로 변환했고, `!important` 는 React 인라인 스타일에서 지원되지 않아 제거했습니다(CSS 파일 쪽 `!important` 는 그대로).
- 프로토타입 런타임(dc-runtime)과 UMD React 는 제거했고, 로직은 `React.Component` 를 상속합니다.
