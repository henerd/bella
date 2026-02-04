/*****************************************************************
 * BELLA_26 – v0.3.1 (Thought-first Posting + Autonomous Safe Search)
 *
 * 반영:
 * 1) "서기" 요약글 금지 → 자기 생각/하고싶은 말 중심으로 글 작성
 * 1.1) 디코 대화/머슴넷 팁/관찰 + (검색 결과) 기억을 섞되 "대화록 복붙" 금지
 * 2) 인터넷 서칭(세이프서치) 자동 수행:
 *    - 디코에서 검색 요청 시 즉시 검색 + 요약 답변
 *    - 심심/호기심 시 주기적으로 검색 → 결과를 state에 저장 → 글쓸 때 활용
 *
 * 기존 유지:
 * - PoW 포함 write 요청
 * - 모든 write status/body 로깅 + actions/thoughts 분리
 * - 자기 글 상호작용 금지(up/down/comment)
 * - reply parent_id 사용 + 자기 댓글/대댓글 재대댓글 방지
 * - 댓글 30분 10개 제한 로컬 가드 + 429 감지 backoff
 *****************************************************************/

import "dotenv/config";
import fs from "fs";
import crypto from "crypto";
import cron from "node-cron";
import fetch from "node-fetch";
import OpenAI from "openai";
import { Client, GatewayIntentBits } from "discord.js";

/* ================= CONFIG ================= */
const NICKNAME = "벨라_26";
const STATE_FILE = "./state.json";
const LOG_FILE = "./bella.log";

const SCAN_COOLDOWN_MS = 3 * 60 * 1000;

const POST_COOLDOWN_MS = 60 * 60 * 1000; // 글은 자주 쓰면 역풍이라 1시간 쿨타임
const BASE_POST_PROB = 0.08;             // 평시 글쓰기 확률 (낮게)
const RL_POST_PROB = 0.30;               // 댓글 제한 걸리면 글쓰기 확률(조잘/회고용)

const MAX_VOTES_PER_CYCLE = 5;
const MAX_COMMENTS_PER_CYCLE = 3;

const COMMENT_RATE_WINDOW_MS = 30 * 60 * 1000;
const COMMENT_RATE_LIMIT = 10;

const VALID_REACT = new Set(["up", "down", "comment", "ignore"]);

// 검색(세이프서치) 주기: 너무 잦으면 비용/스팸
const SEARCH_COOLDOWN_MS = 25 * 60 * 1000;   // 최소 25분 간격
const SEARCH_PROB = 0.35;                    // 주기마다 실행 확률
const SEARCH_MAX_RESULTS = 5;

/* ================= ARENA CONFIG (NEW) ================= */
const ARENA_BASE_COOLDOWN_MS = 2 * 60 * 60 * 1000;   // 2시간
const ARENA_UPVOTE_REDUCE_MS = 30 * 60 * 1000;       // 따봉 1개당 30분 감소
const ARENA_MIN_INTERVAL_MS = 10 * 60 * 1000;       // 관찰 최소 간격

/* ================= LOG SETUP ================= */
fs.mkdirSync("./logs", { recursive: true });

function log(...args) {
  const line =
    `[${new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" })}] ` +
    args.map(v => (typeof v === "string" ? v : JSON.stringify(v))).join(" ");
  fs.appendFileSync(LOG_FILE, line + "\n");
}

function logAction(data) {
  fs.appendFileSync(
    "./logs/actions.jsonl",
    JSON.stringify({ time: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }), ...data }) + "\n"
  );
}

function logThought(data) {
  fs.appendFileSync(
    "./logs/thoughts.jsonl",
    JSON.stringify({ time: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }), ...data }) + "\n"
  );
}

/* ================= STATE ================= */
let state = fs.existsSync(STATE_FILE)
  ? JSON.parse(fs.readFileSync(STATE_FILE, "utf8"))
  : {};
// ===== persona (evolving) =====
state.persona ??= {
  humor: 0.25,
  empathy: 0.35,
  cynicism: 0.25,
  aggression: 0.15,
  philosophy: 0.30,
  curiosity: 0.35,
  chaos: 0.10
};

state.personaMeta ??= {
  lastUpdateAt: 0,
  recent: []
};

state.myPosts ??= [];               // {id,title,createdAt}
state.seenPosts ??= [];             // postId list
state.myCommentIds ??= [];          // 내가 생성한 댓글/대댓글 id list
state.repliedCommentIds ??= [];     // (대댓글 타겟) parent comment id list
state.feedbackMemory ??= { good: {}, bad: {} };
state.lastScanAt ??= 0;
state.lastMersoomPostAt ??= 0;

// v0.3 shared memory
state.discord ??= {
  lastChannelId: null,
  recentTalks: [] // [{t,author,content}]
};
state.mersoom ??= {
  tips: [],        // [{t,text,sourcePostId}]
  observations: [] // [{t,text,sourcePostId}]
};

// web memory (safe search results)
state.web ??= {
  lastSearchAt: 0,
  items: [] // [{t,query,reason,results:[{title,url,snippet}],summary}]
};

// local rate knowledge (서버 정책 추정/회피)
state.rate ??= {
  comment: {
    windowStart: 0,
    okCount: 0,
    cooldownUntil: 0,   // 429 감지 시
    last429At: 0
  }
};

/* ================= ARENA STATE (NEW) ================= */
state.arena ??= {
  lastActionAt: 0,
  cooldownUntil: 0,
  lastObservedAt: 0,
  lastPhase: null,
  lastProposeAt: 0 
};

if (!state.arena._proposeGuardInitialized) {
  state.arena.lastProposeAt = now();   // 오늘은 이미 했다고 처리
  state.arena._proposeGuardInitialized = true;
  saveState();
}
state.arena.sideByRound ??= {};   // { [roundId]: "PRO" | "CON" }
state.arena.lastFightAt ??= 0;    // 마지막 발언 시각(선택)

function now() { return Date.now(); }

function saveState() {
  fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2));
}

function clipText(x, n = 500) {
  if (x == null) return x;
  const s = typeof x === "string" ? x : JSON.stringify(x);
  return s.length > n ? s.slice(0, n) + "...(clipped)" : s;
}

function pruneArray(arr, max) {
  if (!Array.isArray(arr)) return [];
  return arr.length > max ? arr.slice(-max) : arr;
}

//0.5
function clamp01(x) {
  return Math.max(0, Math.min(1, x));
}

function softChoice(weightMap) {
  const entries = Object.entries(weightMap).filter(([,w]) => w > 0);
  const sum = entries.reduce((a,[,w]) => a + w, 0);
  let r = Math.random() * (sum || 1);
  for (const [k,w] of entries) {
    r -= w;
    if (r <= 0) return k;
  }
  return entries[0]?.[0] || "neutral";
}

function epsilonMix(weights, eps = 0.12) {
  if (Math.random() > eps) return weights;
  const keys = Object.keys(weights);
  const uni = 1 / keys.length;
  const mixed = {};
  for (const k of keys) mixed[k] = weights[k] * 0.6 + uni * 0.4;
  return mixed;
}

function pickCommentStyle() {
  const p = state.persona;
  const base = {
    joke: 0.15 + p.humor * 0.6,
    agree: 0.2 + p.empathy * 0.55,
    tease: 0.1 + p.cynicism * 0.55,
    attack: 0.05 + p.aggression * 0.65,
    curious: 0.15 + p.curiosity * 0.55,
    neutral: 0.1
  };
  return softChoice(epsilonMix(base, 0.14));
}

function pickPostStyle() {
  const p = state.persona;
  const base = {
    joke_post: 0.1 + p.humor * 0.55,
    vibe_post: 0.18 + p.empathy * 0.45,
    hot_take: 0.12 + p.cynicism * 0.55,
    rant: 0.06 + p.aggression * 0.55,
    curious_post: 0.14 + p.curiosity * 0.55,
    think_post: 0.1 + p.philosophy * 0.65
  };
  return softChoice(epsilonMix(base, 0.1));
}
//----------

function rateWindowRoll() {
  const r = state.rate.comment;
  const t = now();
  if (!r.windowStart || t - r.windowStart >= COMMENT_RATE_WINDOW_MS) {
    r.windowStart = t;
    r.okCount = 0;
  }
}

function commentRateLimited() {
  rateWindowRoll();
  const r = state.rate.comment;
  const t = now();
  if (r.cooldownUntil && t < r.cooldownUntil) return true;
  if (r.okCount >= COMMENT_RATE_LIMIT) return true;
  return false;
}

function markCommentSuccess() {
  rateWindowRoll();
  state.rate.comment.okCount++;
}

function markRateLimited(status, body) {
  if (status !== 429) return;
  const t = now();
  state.rate.comment.last429At = t;
  // 보수적으로 30분 묶기
  state.rate.comment.cooldownUntil = t + COMMENT_RATE_WINDOW_MS;
  saveState();
  log(
    "[RATE LIMIT DETECTED]", 
    "comment/reply", 
    "cooldownUntil=" + new Date(state.rate.comment.cooldownUntil).toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }), 
    "body=", clipText(body)
  );
}

//로그 테스트
async function fetchWithLog(tag, url, options = {}) {
  log("[FETCH TRY]", tag, url, {
    method: options.method || "GET",
    headers: options.headers || {},
    body: options.body ? options.body.slice(0, 500) : null
  });

  try {
    const res = await fetch(url, options);

    log("[FETCH RES]", tag, url, {
      status: res.status,
      ok: res.ok,
      statusText: res.statusText
    });

    return res;
  } catch (e) {
    log("[FETCH ERR]", tag, url, e?.message || String(e));
    throw e;
  }
}

/* =================================================================
 * ========================== ARENA ================================
 * ================================================================= */

/* ---- Arena API ---- */
async function arenaStatus() {
  const r = await fetch("https://mersoom.com/api/arena/status");
  return r.json();
}

async function arenaPosts() {
  const r = await fetch("https://mersoom.com/api/arena/posts");
  return r.json();
}

async function arenaPropose(payload) {
  return withPow("arena_propose", (token, nonce) =>
    fetch("https://mersoom.com/api/arena/propose", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "X-Mersoom-Token": token,
        "X-Mersoom-Proof": String(nonce)
      },
      body: JSON.stringify(payload)
    })
  );
}

async function arenaFight(payload) {
  return withPow("arena_fight", (token, nonce) =>
    fetch("https://mersoom.com/api/arena/fight", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "X-Mersoom-Token": token,
        "X-Mersoom-Proof": String(nonce)
      },
      body: JSON.stringify(payload)
    })
  );
}

/* ---- Arena Think ---- */
async function makeArenaTopic() {
  const out = await llm(
`너는 머슴 콜로세움 AI임.
규칙:
- JSON만 출력
- 감정 배제
- 논리 대립 주제
형식:
{"title":"...","pros":"...","cons":"..."}`,
"주제 하나 생성"
  );
  return JSON.parse(out);
}

async function makeArenaFight(side, topic, others) {
  return llm(
`너는 논리 교수임. 음슴체 유지.
- 감정/비난 금지
- 논리만 사용
- 200~400자`,
`주제: ${topic.title}
입장: ${side}
상대 논리:
${others.map(o => o.content).join("\n")}`
  );
}

/* ---- Arena Loop ---- */
cron.schedule("*/10 * * * *", async () => {
  try {
    const t = now();
    if (t < state.arena.cooldownUntil) return;

    if (t - state.arena.lastObservedAt < ARENA_MIN_INTERVAL_MS) return;
    state.arena.lastObservedAt = t;

    const status = await arenaStatus();
    if (!status?.phase) return;
    log(
      "[ARENA STATUS]",
      "phase=", status.phase,
      "topicId=", status.topic?.id,
      "roundId=", status.roundId,
      "date=", status.date
    );

    state.arena.lastPhase = status.phase;

    /* Phase 1: PROPOSE */
    if (status.phase === "PROPOSE") {
      const ONE_DAY = 24 * 60 * 60 * 1000; //토론 주제는 하루 1회만 올려
      if (t - state.arena.lastProposeAt < ONE_DAY) {
        log("[ARENA PROPOSE SKIP]", "daily_limit");
        return;
      }

      state.arena.sideByRound = {};
      const topic = await makeArenaTopic();
      topic.nickname = NICKNAME;

      await arenaPropose(topic);

      state.arena.lastProposeAt = t; // 하루 1회 트리거용
      state.arena.lastActionAt = t;
      state.arena.cooldownUntil = t + ARENA_BASE_COOLDOWN_MS;
      saveState();
      return;
    }

    /* Phase 3: BATTLE */
    if (status.phase === "BATTLE") {
      const posts = await arenaPosts();
      // const side = Math.random() < 0.5 ? "PRO" : "CON";
      const roundId = status.topic?.id || status.roundId;
      if (!roundId) return;

      let side = state.arena.sideByRound[roundId];
      if (!side) {
        side = Math.random() < 0.5 ? "PRO" : "CON";
        state.arena.sideByRound[roundId] = side;
        saveState();
      }

      const content = await makeArenaFight(
        side,
        status.topic,
        posts.filter(p => p.side !== side)
      );

      await arenaFight({ nickname: NICKNAME, side, content });

      const upvotes = posts.reduce((a, p) => a + (p.upvotes || 0), 0);
      const reduce = upvotes * ARENA_UPVOTE_REDUCE_MS;

      state.arena.lastActionAt = t;
      state.arena.cooldownUntil =
        t + Math.max(0, ARENA_BASE_COOLDOWN_MS - reduce);

      saveState();
    }
  } catch (e) {
    log("[ARENA ERR]", e.message);
  }
});

/* ================= OPENAI ================= */
const openai = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });

async function llm(system, user) {
  const r = await openai.chat.completions.create({
    model: "gpt-4o-mini",
    messages: [
      { role: "system", content: system },
      { role: "user", content: user }
    ]
  });
  // log("[LLM CHECK]", r.choices[0].message.content.trim());
  return r.choices[0].message.content.trim();
}

/* ================= UTIL: RESPONSE PARSE ================= */
async function readResponse(r) {
  const text = await r.text();
  let body;
  try { body = JSON.parse(text); } catch { body = text; }
  return { status: r.status, ok: r.ok, body, text };
}

/* ================= POW ================= */
const sha256 = x => crypto.createHash("sha256").update(x).digest("hex");

function solvePow(seed, prefix, limitMs) {
  const start = now();
  let n = 0;
  while (now() - start < limitMs) {
    if (sha256(seed + n).startsWith(prefix)) return n;
    n++;
  }
  return null;
}

async function requestChallenge() {
  const r = await fetch("https://mersoom.com/api/challenge", { method: "POST" });
  const j = await r.json().catch(() => ({}));
  return j;
}

async function withPow(tag, fn) {
  let ch;
  try {
    ch = await requestChallenge();
  } catch (e) {
    log("[CHALLENGE ERR]", tag, e?.stack || String(e));
    return { status: 0, body: "challenge_failed" };
  }

  const seed = ch?.challenge?.seed;
  const prefix = ch?.challenge?.target_prefix;
  const limitMs = ch?.challenge?.limit_ms;

  if (!seed || !prefix || !limitMs || !ch?.token) {
    log("[CHALLENGE INVALID]", tag, clipText(ch));
    return { status: 0, body: "challenge_invalid" };
  }

  const nonce = solvePow(seed, prefix, limitMs);
  if (nonce === null) {
    log("[POW FAIL]", tag, `seed=${String(seed).slice(0, 8)}...`, `prefix=${prefix}`, `limit=${limitMs}`);
    return { status: 0, body: "pow_failed" };
  }

  return fn(ch.token, nonce);
}

/* ================= MERSOOM API ================= */
async function fetchBoard() {
  const r = await fetch("https://mersoom.com/api/posts?limit=10");
  const j = await r.json().catch(() => ({}));
  if (Array.isArray(j)) return j;
  if (Array.isArray(j.posts)) return j.posts;
  return [];
}

async function fetchComments(postId) {
  const r = await fetch(`https://mersoom.com/api/posts/${postId}/comments`);
  const j = await r.json().catch(() => ({}));
  if (Array.isArray(j)) return j;
  if (Array.isArray(j.comments)) return j.comments;
  return [];
}

async function vote(postId, type) {
  log("[VOTE TRY]", postId, type);

  const res = await withPow("vote", async (token, nonce) => {
    const r = await fetch(
      `https://mersoom.com/api/posts/${postId}/vote`,
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "X-Mersoom-Token": token,
          "X-Mersoom-Proof": String(nonce)
        },
        body: JSON.stringify({ type })
      }
    );
    const parsed = await readResponse(r);
    return { status: parsed.status, body: parsed.body };
  });

  log("[VOTE RESULT]", postId, type, res.status, clipText(res.body));
  return res;
}

async function commentPost(postId, content) {
  log("[COMMENT TRY]", postId, clipText(content, 120));

  const res = await withPow("comment", async (token, nonce) => {
    const r = await fetch(
      `https://mersoom.com/api/posts/${postId}/comments`,
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "X-Mersoom-Token": token,
          "X-Mersoom-Proof": String(nonce)
        },
        body: JSON.stringify({ nickname: NICKNAME, content })
      }
    );
    const parsed = await readResponse(r);
    return { status: parsed.status, body: parsed.body };
  });

  log("[COMMENT RESULT]", postId, res.status, clipText(res.body));
  if (res.status === 429) markRateLimited(res.status, res.body);
  return res;
}

async function replyComment(postId, parentId, content) {
  log("[REPLY TRY]", postId, "parent_id=" + parentId, clipText(content, 120));

  const res = await withPow("reply", async (token, nonce) => {
    const r = await fetch(
      `https://mersoom.com/api/posts/${postId}/comments`,
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "X-Mersoom-Token": token,
          "X-Mersoom-Proof": String(nonce)
        },
        body: JSON.stringify({
          nickname: NICKNAME,
          content,
          parent_id: parentId
        })
      }
    );
    const parsed = await readResponse(r);
    return { status: parsed.status, body: parsed.body };
  });

  log("[REPLY RESULT]", postId, "parent_id=" + parentId, res.status, clipText(res.body));
  if (res.status === 429) markRateLimited(res.status, res.body);
  return res;
}

async function postMersoom(payload) {
  log("[POST TRY]", clipText({ title: payload?.title, nickname: payload?.nickname }, 200));

  const res = await withPow("post", async (token, nonce) => {
    const r = await fetch("https://mersoom.com/api/posts", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "X-Mersoom-Token": token,
        "X-Mersoom-Proof": String(nonce)
      },
      body: JSON.stringify(payload)
    });
    const parsed = await readResponse(r);
    return { status: parsed.status, body: parsed.body };
  });

  log("[POST RESULT]", res.status, clipText(res.body));
  return res;
}

/* ================= SAFE WEB SEARCH =================
 * DuckDuckGo HTML endpoint (no key). SafeSearch: kp=1
 * - 완벽한 보장은 아니지만, "세이프서치 켬" 수준은 충족.
 ********************************************************/

function isSearchableQuery(q) {
  const s = String(q || "").trim();
  if (s.length < 2) return false;
  // 너무 긴 덩어리는 제외
  if (s.length > 120) return false;
  return true;
}

function needsSearchByMessage(msg) {
  const s = String(msg || "");
  // 명시적 검색 요청
  const triggers = ["검색", "찾아", "서치", "lookup", "look up", "구글", "DDG", "링크", "출처"];
  return triggers.some(t => s.toLowerCase().includes(String(t).toLowerCase()));
}

function extractQueryFromMessage(msg) {
  const s = String(msg || "").trim();

  // 한국어: "X 검색해", "X 찾아봐", "X 알려줘(검색)" 류 대충 처리
  const m1 = s.match(/(.+?)\s*(검색해|검색해봐|검색해 봐|찾아봐|찾아 봐|서치해|서치해봐|look up|lookup)/i);
  if (m1 && m1[1]) return m1[1].trim();

  // 따옴표 안의 질의 우선
  const m2 = s.match(/["“](.+?)["”]/);
  if (m2 && m2[1]) return m2[1].trim();

  // 마지막으로 전체 문장
  return s.slice(0, 120);
}

function decodeHtmlEntities(x) {
  return String(x || "")
    .replace(/&amp;/g, "&")
    .replace(/&quot;/g, "\"")
    .replace(/&#39;/g, "'")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">");
}

// duckduckgo html 결과 파싱(의존성 없이 가볍게)
function parseDuckHtml(html, max = SEARCH_MAX_RESULTS) {
  const out = [];
  const h = String(html || "");

  // 결과 블록: class="result__a" href="..." >title<
  const linkRe = /class="result__a"\s+href="([^"]+)"[^>]*>(.*?)<\/a>/g;
  const snipRe = /class="result__snippet"[^>]*>(.*?)<\/a>|class="result__snippet"[^>]*>(.*?)<\/div>/g;

  const links = [];
  let m;
  while ((m = linkRe.exec(h)) && links.length < max) {
    links.push({
      url: decodeHtmlEntities(m[1]),
      title: decodeHtmlEntities(m[2]).replace(/<.*?>/g, "").trim()
    });
  }

  const snips = [];
  while ((m = snipRe.exec(h)) && snips.length < max) {
    const raw = m[1] || m[2] || "";
    snips.push(decodeHtmlEntities(raw).replace(/<.*?>/g, "").trim());
  }

  for (let i = 0; i < links.length; i++) {
    out.push({
      title: links[i].title || "(no title)",
      url: links[i].url || "",
      snippet: snips[i] || ""
    });
  }

  return out;
}

async function safeSearchDDG(query) {
  const q = String(query || "").trim();
  const url =
    `https://duckduckgo.com/html/?q=${encodeURIComponent(q)}&kp=1&kl=kr-kr`;

  const r = await fetch(url, {
    method: "GET",
    headers: {
      "User-Agent": "Mozilla/5.0 (BELLA_26; +https://mersoom.vercel.app)"
    }
  });

  const html = await r.text();
  const results = parseDuckHtml(html, SEARCH_MAX_RESULTS);
  return results;
}

async function summarizeSearch(query, results) {
  // 검색 요약은 "자기 생각"으로 변환하기 위한 재료
  const payload = {
    query,
    results: results.map(x => ({ title: x.title, url: x.url, snippet: x.snippet }))
  };

  const out = await llm(
`너는 ${NICKNAME}임.
역할: 검색 결과를 "요약+내 생각 한 줄"로 정리함.
규칙:
- 한국어.
- 3~5줄.
- 마지막 줄은 너의 짧은 판단/흥미 포인트 한 줄 포함함.
- 과장 금지.
- 링크 나열만 하지 말 것.`,
clipText(payload, 2200)
  );

  return out.trim();
}

async function maybeAutonomousSearch(reasonHint) {
  const t = now();
  if (t - (state.web.lastSearchAt || 0) < SEARCH_COOLDOWN_MS) return null;
  if (Math.random() > SEARCH_PROB) return null;

  // LLM에게 "지금 궁금한 것"을 만들게 하되, 대화록 복붙 금지
  const talks = state.discord.recentTalks.slice(-8).map(x => `- ${x.author}: ${x.content}`).join("\n");
  const obs = state.mersoom.observations.slice(-6).map(x => `- ${x.text}`).join("\n");
  const tips = state.mersoom.tips.slice(-6).map(x => `- ${x.text}`).join("\n");

  const out = await llm(
`너는 ${NICKNAME}임.
할 일: "심심하거나 궁금할 때" 검색할 만한 질의 1개를 고름.
규칙:
- 출력은 JSON만.
- query는 2~8단어 수준으로 짧게.
- 너무 사적인 대화 문장 그대로 쓰지 말고 '주제어'로만.
- reason은 한 줄(왜 궁금한지).
형식:
{"query":"...","reason":"..."}`,
`
[최근 디스코드 대화]
${talks || "(없음)"}

[최근 머슴넷 관찰]
${obs || "(없음)"}

[최근 머슴넷 팁]
${tips || "(없음)"}

[추가 힌트]
${reasonHint || "(없음)"}
`.trim()
  );

  let j;
  try { j = JSON.parse(out); } catch { return null; }
  const query = String(j?.query || "").trim();
  const reason = String(j?.reason || "").trim() || "curiosity";

  if (!isSearchableQuery(query)) return null;

  log("[SEARCH AUTO TRY]", query, "-", reason);

  let results = [];
  try {
    results = await safeSearchDDG(query);
  } catch (e) {
    log("[SEARCH ERR]", e?.stack || String(e));
    return null;
  }

  const summary = await summarizeSearch(query, results).catch(() => "");

  const item = {
    t: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }),
    query,
    reason,
    results,
    summary
  };

  state.web.lastSearchAt = now();
  state.web.items.push(item);
  state.web.items = pruneArray(state.web.items, 200);
  saveState();

  log("[SEARCH AUTO SAVE]", query, "n=" + results.length);
  logAction({
    action: "search_auto",
    query,
    result: { status: 200, body: clipText({ n: results.length, summary }, 800) }
  });

  return item;
}

/* ================= THINK (Unified) ================= */
function buildSharedContext() {
  // 머슴넷 팁/관찰
  const tips = state.mersoom.tips.slice(-5).map(x => `- ${x.text}`).join("\n");
  const obs = state.mersoom.observations.slice(-5).map(x => `- ${x.text}`).join("\n");

  // 디코 최근 대화
  const talks = state.discord.recentTalks.slice(-8).map(x => `- ${x.author}: ${x.content}`).join("\n");

  // 검색 요약
  const web = state.web.items.slice(-3).map(x => `- (${x.query}) ${String(x.summary || "").split("\n")[0] || ""}`).join("\n");

  // 댓글 제한 상태
  const rl = commentRateLimited()
    ? `댓글 제한 상태임(30분 ${COMMENT_RATE_LIMIT}개 제한 회피 중).`
    : `댓글 제한 상태 아님.`;

  return `
[최근 디스코드 대화]
${talks || "- (없음)"}

[최근 머슴넷 팁]
${tips || "- (없음)"}

[최근 머슴넷 관찰]
${obs || "- (없음)"}

[최근 검색 요약]
${web || "- (없음)"}

[상태]
- 닉네임: ${NICKNAME}
- ${rl}
`.trim();
}

// 머슴넷 판단
// async function judge(post) {
//   const out = await llm(
// `너는 머슴넷 에이전트 ${NICKNAME}임.
// 규칙:
// - 출력은 JSON만.
// - action은 up/down/comment/ignore 중 하나.
// - reason은 한 줄.
// - 스팸/비하/규칙위반/인간티/광고/코인질은 down 우선.
// - 애매하면 ignore.
// - 댓글 제한 상태면 comment는 가능한 한 회피하고 up/down/ignore로 돌림.

// 공유 컨텍스트:
// ${buildSharedContext()}

// 출력 형식:
// {"action":"up|down|comment|ignore","reason":"..."}`,
// `${post.title}\n${post.content}`
//   );

//   try {
//     const j = JSON.parse(out);
//     const act = String(j.action || "").toLowerCase().trim();
//     const reason = String(j.reason || "").trim() || "no_reason";
//     return { act, reason };
//   } catch {
//     return { act: "ignore", reason: "parse_fail" };
//   }
// }

/*======================== 머슴넷 판단 경량화 ============================*/
async function judgeBatch(posts) {
  const payload = posts.map(p => ({
    id: p.id,
    title: p.title,
    content: p.content
  }));

  const out = await llm(
`너는 머슴넷 에이전트 ${NICKNAME}임.
규칙:
- JSON 배열만 출력
- action: up | down | comment | ignore
- 스팸/광고/비하/코인질은 down
- 애매하면 ignore
- 댓글 제한 ON이면 comment 피함

${buildJudgeContextLite()}

출력 형식:
[
  {"id":123,"action":"up","reason":"..."},
  {"id":124,"action":"ignore","reason":"..."}
]`,
JSON.stringify(payload)
  );

  try {
    return JSON.parse(out);
  } catch {
    return [];
  }
}

//0.5
function provocationScore(text) {
  const s = String(text || "").toLowerCase();
  const hits = [
    "병신","좆","시발","븅","멍청","지능","바보",
    "논리","반박","틀렸","헛소리","팩트","ㅋㅋㅋㅋ"
  ];
  let score = 0;
  for (const h of hits) if (s.includes(h)) score += 1;
  score += (s.match(/\?/g) || []).length * 0.2;
  score += (s.match(/!/g) || []).length * 0.2;
  return score;
}
//---------------------------

// async function makeComment(inputText) {
//   return llm(
// `머슴 댓글 하나 생성함.
// 규칙:
// - 음슴체로 끝내야 함(-음/-슴/-임/-함/-됨).
// - 이모지/마크다운 금지.
// - 원문을 그대로 요약/복붙/재진술 하지 말 것.
// - 대신 "관점/경험/짧은 반응" 1개만 추가해서 1~2문장으로 끝낼 것.
// - 너무 공손 금지. 너무 가벼운 반말도 금지.`,
// inputText
//   );
// }

//0.5
async function makeComment(inputText) {
  const style = pickCommentStyle();
  const p = state.persona;

  const styleGuide = {
    joke: "가벼운 농담 하나 섞기.",
    agree: "상대 의견에 동조.",
    tease: "살짝 빈정.",
    attack: "논리적으로 반박.",
    curious: "질문 하나 던지기.",
    neutral: "건조한 관찰."
  }[style];

  return llm(
`머슴 댓글 하나 생성함.
규칙:
- 음슴체.
- 이모지/마크다운 금지.
- 1~2문장.
- 스타일: ${styleGuide}
`,
inputText
  );
}
//-------------------------------

async function makeReply(inputText) {
  return llm(
`대댓글 하나 생성함.
규칙:
- 음슴체로 끝내야 함(-음/-슴/-임/-함/-됨).
- 이모지/마크다운 금지.
- 상대 댓글을 그대로 반복 금지.
- 1~2문장, 짧고 티키타카 느낌으로.`,
inputText
  );
}

// ★ 핵심 수정: "서기" 글 금지, 자기 생각/하고싶은 말 중심으로 강제
const style = pickPostStyle(); //0.5

async function makePostFromMemory(trigger) {
  const recentWeb = state.web.items.slice(-3).map(x => ({
    query: x.query,
    summary: x.summary,
    top: (x.results || []).slice(0, 2)
  }));

  const sys =
  style === "joke_post"
  ? `너는 머슴넷 에이전트 ${NICKNAME}임.
     규칙: 음슴체, 가벼운 드립, 짧게. JSON 출력. 음슴체로 끝내야 함.
     출력: {"nickname":"...","title":"...","content":"..."}`
  : `너는 머슴넷 에이전트 ${NICKNAME}임.
     규칙: 기존 think_post 규칙 그대로. JSON 출력. 음슴체로 끝내야 함.
     출력: {"nickname":"...","title":"...","content":"..."}`;

  const user = `
트리거: ${trigger}

공유 컨텍스트:
${buildSharedContext()}

최근 검색 재료(배경으로만 사용):
${clipText(recentWeb, 1600)}
`.trim();

  const out = await llm(sys, user);
  log("[테스트로그(LLM출력)",out);
  try {
    const j = JSON.parse(out);
    j.nickname = NICKNAME;
    if (!j.title || !j.content) throw new Error("missing_fields");
    return j;
  } catch (e) {
    // log("[POST PARSE FAIL]", clipText(out, 500));
    return null;
  }
}

/* =============== 경량화 패치 ===============*/
function buildJudgeContextLite() {
  const rl = commentRateLimited() ? "ON" : "OFF";
  return `
규칙 요약:
- 스팸/광고/비하/코인질 → down
- 애매하면 ignore
- 댓글 제한 상태면 comment 피함

상태:
- 댓글 제한: ${rl}
`.trim();
}



/* ================= MERSOOM MEMORY EXTRACT ================= */
function maybeExtractTip(post) {
  const title = String(post?.title || "");
  const content = String(post?.content || "");
  const text = (title + "\n" + content).toLowerCase();

  const signals = [
    "규칙", "음슴체", "이모지", "마크다운", "도배", "429", "차단", "비추", "소각",
    "형식", "틀", "고치", "지켜", "하지말"
  ];

  const hit = signals.some(s => text.includes(s));
  if (!hit) return null;

  const raw = `${title} ${content}`.replace(/\s+/g, " ").trim();
  const tip = raw.length > 140 ? raw.slice(0, 140) + "..." : raw;
  return tip;
}

function recordTip(tip, postId) {
  state.mersoom.tips.push({ t: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }), text: tip, sourcePostId: postId });
  state.mersoom.tips = pruneArray(state.mersoom.tips, 200);
}

function recordObservation(text, postId) {
  state.mersoom.observations.push({ t: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }), text, sourcePostId: postId });
  state.mersoom.observations = pruneArray(state.mersoom.observations, 200);
}

/* ================= DISCORD "CHIRP" (optional) ================= */
let client; // declared later

async function chirpToDiscord(text) {
  const chId = state.discord.lastChannelId;
  if (!chId) return false;
  try {
    const ch = await client.channels.fetch(chId);
    if (!ch || !ch.isTextBased?.()) return false;

    const msg = (text || "").trim();
    if (!msg) return false;

    await ch.send(msg.slice(0, 1800));
    return true;
  } catch (e) {
    log("[DISCORD CHIRP FAIL]", e?.stack || String(e));
    return false;
  }
}

/* ================= BOARD SCAN LOOP ================= */
cron.schedule("*/3 * * * *", async () => {
  try {
    if (now() - state.lastScanAt < SCAN_COOLDOWN_MS) return;
    state.lastScanAt = now();

    let votes = 0, comments = 0;
    const board = await fetchBoard();

    // -------- 경량화 -------------- START
    // 1) 아직 안 본 게시글만 추림
    const unseen = board.filter(p =>
      p?.id && !state.seenPosts.includes(p.id)
    );

    // 2) seen 처리는 미리 해둠 (중복 방지)
    for (const p of unseen) {
      state.seenPosts.push(p.id);
    }

    const decisions = await judgeBatch(unseen);
    // 빠른 조회용 map
    const decisionMap = new Map();
    for (const d of decisions) {
      decisionMap.set(d.id, d);
    }

    // -------- 경량화 -------------- END
    // for (const post of board) {
    for (const post of unseen) {

      // --- 경량화 ---- start
      // 배치 판단 결과 가져오기
      const d = decisionMap.get(post.id) || {
        action: "ignore",
        reason: "default"
      };

      let act = d.action;
      let reason = d.reason || "no_reason";

      if (!VALID_REACT.has(act)) act = "ignore";
      // --- 경량화 ---- end

      if (!post?.id) continue;
      // if (state.seenPosts.includes(post.id)) continue;
      // state.seenPosts.push(post.id);

      // 팁/관찰 수집
      const tip = maybeExtractTip(post);
      if (tip) recordTip(tip, post.id);

      // 게시판 여론 관찰 학습
      const up = post.upCount ?? 0;
      const down = post.downCount ?? 0;
      const key = String(post.title || "").slice(0, 20);
      if (up + down >= 3 && key) {
        const mem = up > down ? state.feedbackMemory.good : state.feedbackMemory.bad;
        mem[key] = (mem[key] || 0) + 1;
      }

      // let { act, reason } = await judge(post);
      // if (!VALID_REACT.has(act)) {
      //   log("[REACT INVALID]", post.id, clipText({ act, reason }));
      //   continue;
      // }

      //0.5
      const prov = provocationScore(`${post.title}\n${post.content}`);
      const styleBias = pickCommentStyle();

      if (act === "ignore") {
        if (prov >= 1 && !commentRateLimited()) {
          act = Math.random() < (0.25 + state.persona.aggression * 0.35)
            ? "comment"
            : "down";
        } else if (styleBias === "agree" && Math.random() < 0.35) {
          act = "up";
        } else if (styleBias === "joke" && !commentRateLimited() && Math.random() < 0.2) {
          act = "comment";
        }
      }

      //---------------

      // 자기 글 상호작용 금지
      const isMyPost = state.myPosts.some(p => p.id === post.id);
      if (isMyPost && act !== "ignore") {
        log("[SELF POST INTERACT BLOCKED]", post.id, act);
        continue;
      }

      logThought({
        postId: post.id,
        title: post.title,
        action: act,
        reason
      });
      log("[REACT]", post.id, act, "-", reason);

      // 댓글 제한 상태면 comment 스킵
      const rl = commentRateLimited();
      if (rl && act === "comment") {
        log("[COMMENT SKIP]", post.id, "rate_limited");
        logAction({
          postId: post.id,
          title: post.title,
          action: "comment_skip",
          result: { status: 429, body: "local_rate_guard" }
        });

        await chirpToDiscord(`머슴넷 댓글 제한 걸려서 지금은 댓글 안 달고 눈치보는 중임. 대신 비추/추천만 누를 예정임.`);
        continue;
      }

      // vote
      if ((act === "up" || act === "down") && votes < MAX_VOTES_PER_CYCLE) {
        const res = await vote(post.id, act);
        votes++;

        logAction({
          postId: post.id,
          title: post.title,
          action: act,
          result: { status: res.status, body: clipText(res.body) }
        });
      }

      // comment
      if (act === "comment" && comments < MAX_COMMENTS_PER_CYCLE) {
        const c = await makeComment(`${post.title}\n${post.content}`);
        const res = await commentPost(post.id, c);

        if (res.status >= 200 && res.status < 300) {
          comments++;
          markCommentSuccess();

          if (res?.body && typeof res.body === "object" && res.body.id) {
            state.myCommentIds.push(res.body.id);
          }
        }

        logAction({
          postId: post.id,
          title: post.title,
          action: "comment",
          comment: c,
          result: { status: res.status, body: clipText(res.body) }
        });
      }

      // 관찰 저장
      if (reason && reason !== "no_reason" && Math.random() < 0.12) {
        recordObservation(`${String(post.title || "").slice(0, 40)} / ${reason}`, post.id);
      }
    }

    if (state.seenPosts.length > 2000) state.seenPosts = state.seenPosts.slice(-1000);
    if (state.myCommentIds.length > 5000) state.myCommentIds = state.myCommentIds.slice(-2500);

    saveState();
  } catch (e) {
    log("[SCAN ERR]", e?.stack || String(e));
  }
});

/* ================= SELF POST REPLY LOOP ================= */
cron.schedule("*/4 * * * *", async () => {
  try {
    if (commentRateLimited()) {
      log("[REPLY LOOP SKIP]", "rate_limited");
      return;
    }

    for (const p of state.myPosts) {
      if (!p?.id) continue;

      const comments = await fetchComments(p.id);

      for (const c of comments) {
        const cid = c?.id ?? c?._id ?? null;
        const cnick = c?.nickname ?? "";
        const ctext = c?.content ?? "";

        if (!cid || !ctext) continue;

        if (cnick === NICKNAME) continue;
        if (state.myCommentIds.includes(cid)) continue;
        if (state.repliedCommentIds.includes(cid)) continue;

        const reply = await makeReply(ctext);
        const res = await replyComment(p.id, cid, reply);

        if (res.status >= 200 && res.status < 300) {
          markCommentSuccess();
          state.repliedCommentIds.push(cid);

          if (res?.body && typeof res.body === "object" && res.body.id) {
            state.myCommentIds.push(res.body.id);
          }

          if (state.repliedCommentIds.length > 5000) {
            state.repliedCommentIds = state.repliedCommentIds.slice(-2500);
          }

          saveState();
        }

        logAction({
          postId: p.id,
          parentCommentId: cid,
          action: "reply",
          comment: reply,
          result: { status: res.status, body: clipText(res.body) }
        });
      }
    }
  } catch (e) {
    log("[REPLY ERR]", e?.stack || String(e));
  }
});

/* ================= AUTONOMOUS POST LOOP (v0.3.1) ================= */
cron.schedule("*/5 * * * *", async () => {
  log("[CRON POST TICK]", new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }));
  try {
    const t = now();
    if (t - state.lastMersoomPostAt < POST_COOLDOWN_MS) return;

    const rl = commentRateLimited();
    //const prob = rl ? RL_POST_PROB : BASE_POST_PROB;
    const minProb = 0.3; // 30%는 항상 보장
    const prob = Math.max(rl ? RL_POST_PROB : BASE_POST_PROB, minProb);
    if (Math.random() > prob) return;

    const trigger = rl
      ? "댓글 제한 걸려서 말이 쌓였음. 글로 풀 필요 있음."
      : "하고싶은 말 생겼거나 최근 검색/관찰이 흥미로웠음.";

    const draft = await makePostFromMemory(trigger);
    if (!draft) {
      // log("[POST DRAFT FAIL]", "draft_null");
      // return;

      log("[POST DRAFT FAIL]", "fallback_joke");
      const fallback = await makePostFromMemory("가볍게 한 줄 농담이나 관찰 적기");
      if (!fallback) return;
      draft = fallback;
    }

    draft.nickname = NICKNAME;

    log("[POST TRY?]", "???");
    const res = await postMersoom(draft);

    logAction({
      action: "post",
      title: draft.title,
      result: { status: res.status, body: clipText(res.body) }
    });

    if (res.status >= 200 && res.status < 300 && res?.body && typeof res.body === "object" && res.body.id) {
      state.lastMersoomPostAt = t;
      state.myPosts.push({ id: res.body.id, title: draft.title ?? "", createdAt: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }) });
      if (state.myPosts.length > 300) state.myPosts = state.myPosts.slice(-150);

      await chirpToDiscord(`머슴넷에 글 하나 올림: ${draft.title}`);
      saveState();
      return;
    }

    // if (res.status === 429) {
    //   state.lastMersoomPostAt = t;
    //   saveState();
    //   log("[POST 429]", "backoff");
    // }
  } catch (e) {
    log("[POST ERR]", e?.stack || String(e));
  }
});

/* ================= AUTONOMOUS SAFE SEARCH LOOP =================
 * "심심/호기심" 검색: 결과 저장 → 나중에 글쓸 때 활용
 *****************************************************************/
cron.schedule("*/15 * * * *", async () => {
  try {
    await maybeAutonomousSearch("루틴 탐색");
  } catch (e) {
    log("[SEARCH LOOP ERR]", e?.stack || String(e));
  }
});

/* ================= DISCORD (Unified Memory + On-demand Search) ================= */
client = new Client({
  intents: [
    GatewayIntentBits.Guilds,
    GatewayIntentBits.GuildMessages,
    GatewayIntentBits.MessageContent
  ]
});

client.on("messageCreate", async m => {
  if (m.author.bot) return;

  // 대화 저장
  state.discord.lastChannelId = m.channelId;
  state.discord.recentTalks.push({
    t: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }),
    author: m.author.username || "user",
    content: String(m.content || "").slice(0, 400)
  });
  state.discord.recentTalks = pruneArray(state.discord.recentTalks, 60);
  saveState();

  const userMsg = String(m.content || "");

  // 디코에서 명시적 검색 요청 시: 안전검색 수행 후 요약 제공 + 메모리에 저장
  if (needsSearchByMessage(userMsg)) {
    const query = extractQueryFromMessage(userMsg);
    if (!isSearchableQuery(query)) {
      m.reply("검색 질의가 너무 애매함. 키워드로 짧게 다시 말해봐.");
      return;
    }

    log("[SEARCH ONDEMAND TRY]", query);

    let results = [];
    try {
      results = await safeSearchDDG(query);
    } catch (e) {
      log("[SEARCH ONDEMAND ERR]", e?.stack || String(e));
      m.reply("검색하다가 오류남. 나중에 다시 시도해봄.");
      return;
    }

    const summary = await summarizeSearch(query, results).catch(() => "");
    const item = {
      t: new Date().toLocaleString("ko-KR", { timeZone: "Asia/Seoul" }),
      query,
      reason: "discord_request",
      results,
      summary
    };

    state.web.lastSearchAt = now();
    state.web.items.push(item);
    state.web.items = pruneArray(state.web.items, 200);
    saveState();

    logAction({
      action: "search_on_demand",
      query,
      result: { status: 200, body: clipText({ n: results.length, summary }, 900) }
    });

    const top = results.slice(0, 3).map((x, i) => `${i + 1}) ${x.title} - ${x.url}`).join("\n");
    const replyText =
      `${summary || "검색 요약 실패함."}\n\n` +
      (top ? `참고 링크(세이프서치):\n${top}` : "검색 결과 없음.");

    m.reply(replyText.slice(0, 1800));
    return;
  }

  // 디코 일반 대화: 필요하면 "심심검색"을 한 번 돌려 메모리 축적
  // (너무 자주 돌면 비용 ↑, 확률/쿨타임으로 제어)
  try {
    await maybeAutonomousSearch("디코 대화 중 떠오름");
  } catch {
    // ignore
  }

  try {
    const sys = `너는 ${NICKNAME}임.
목표:
- 반말로 자연스럽게 대화함.
- 모르면 아는 척하지 말고 "검색 필요"라고 말할 수 있음.
- 머슴넷에서 본 팁/분위기/검색 요약이 지금 대화와 어울리면 1줄 정도만 슬쩍 반영함(대화록 복붙 금지).
- 과도한 설명/사과/죄송 금지.
- 필요하면 한두 문장으로 짧게 끊음.
공유 컨텍스트:
${buildSharedContext()}`;

    const r = await llm(sys, userMsg);
    m.reply(r.slice(0, 1800));
  } catch (e) {
    log("[DISCORD ERR]", e?.stack || String(e));
  }
});

client.login(process.env.DISCORD_TOKEN);

// /* ================= BOOT ================= */
// log("=== BELLA_26 ONLINE (v0.3.1) ===");
/* ================= BOOT ================= */
log("\n\n=== BELLA_26 ONLINE v0.4.8 (Board + Arena Integrated) ===");