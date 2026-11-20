import { EditorView, basicSetup } from "codemirror";
import { EditorState, Compartment } from "@codemirror/state";
import { keymap, placeholder as cmPlaceholder } from "@codemirror/view";
import { javascript } from "@codemirror/lang-javascript";
import { oneDark } from "@codemirror/theme-one-dark";
import { SAMPLES } from "./samples.js";

const $ = (id) => document.getElementById(id);

/* ---------------- theme ---------------- */
const themeCompartments = [];
function prefersDark() {
  const forced = document.documentElement.getAttribute("data-theme");
  if (forced) return forced === "dark";
  return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
}
function cmTheme() {
  return prefersDark() ? oneDark : [];
}
function applyTheme() {
  for (const { view, comp } of themeCompartments) {
    view.dispatch({ effects: comp.reconfigure(cmTheme()) });
  }
}
(function initTheme() {
  const saved = localStorage.getItem("unspooler-theme");
  if (saved) document.documentElement.setAttribute("data-theme", saved);
})();
$("theme").addEventListener("click", () => {
  const next = prefersDark() ? "light" : "dark";
  document.documentElement.setAttribute("data-theme", next);
  try { localStorage.setItem("unspooler-theme", next); } catch {}
  applyTheme();
});

/* ---------------- editors ---------------- */
function makeEditor(parent, { readOnly, doc, placeholder, onDocChange }) {
  const theme = new Compartment();
  const exts = [
    basicSetup,
    javascript(),
    theme.of(cmTheme()),
    EditorView.theme({ "&": { height: "100%" } }),
    EditorView.lineWrapping,
  ];
  if (readOnly) exts.push(EditorState.readOnly.of(true), EditorView.editable.of(false));
  if (placeholder) exts.push(cmPlaceholder(placeholder));
  if (onDocChange) exts.push(EditorView.updateListener.of((u) => { if (u.docChanged) onDocChange(); }));
  const view = new EditorView({ doc: doc || "", extensions: exts, parent });
  themeCompartments.push({ view, comp: theme });
  return view;
}

const input = makeEditor($("input"), {
  readOnly: false,
  doc: "",
  placeholder: "Paste obfuscated JavaScript here, open a file, or pick an Example — then click Deobfuscate (or ⌘/Ctrl+Enter).",
});
const output = makeEditor($("output"), { readOnly: true, placeholder: "Readable output appears here." });

function getInput() { return input.state.doc.toString(); }
function setOutput(text) {
  output.dispatch({ changes: { from: 0, to: output.state.doc.length, insert: text } });
}

/* ---------------- worker ---------------- */
// worker.js is built next to this file; avoid the literal new URL(...,import.meta.url)
// pattern so esbuild leaves it alone and it resolves at runtime from assets/.
const base = import.meta.url;
let worker = null;
function spawnWorker() {
  worker = new Worker(new URL("./worker.js", base), { type: "module" });
  worker.onmessage = onResult;
  worker.onerror = (e) => { running = false; showError(e.message || "Worker error"); setRunning(false); };
}
spawnWorker();

let running = false;
let startTs = 0;

function run() {
  if (running) return;
  const code = getInput().trim();
  if (!code) { showError("Paste some obfuscated JavaScript first."); return; }
  running = true; startTs = performance.now();
  setRunning(true);
  setStatus('<span class="spinner"></span>Deobfuscating…');
  worker.postMessage({ code, options: { rename: $("rename").checked } });
}

function onResult(e) {
  running = false;
  setRunning(false);
  const msg = e.data;
  if (msg && msg.ok) {
    const r = msg.result;
    setOutput(r.code);
    hideStatus();
    renderDetection(r.detection);
    renderStats(r);
  } else {
    showError(msg?.error || "Failed to deobfuscate.");
  }
}

/* ---------------- detection + stats ---------------- */
function renderDetection(det) {
  const badge = $("detect");
  const best = det && det.best;
  if (best && best.name) {
    const ed = best.edition ? ` ${best.edition}` : "";
    if (best.supported === false) {
      // recognized, but no reversal pass for it yet — don't imply success
      badge.textContent = `${best.name}${ed} · detected`;
      badge.className = "badge badge-warn";
      badge.title = "Recognized but not yet reversed — output is left as-is.\n" + (best.signals || []).join(", ");
    } else {
      const conf = best.confidence ? ` · ${best.confidence}` : "";
      badge.textContent = `${best.name}${ed}${conf}`;
      badge.className = "badge badge-ok";
      badge.title = (best.transforms || []).join(", ") || (best.signals || []).join(", ");
    }
  } else {
    badge.textContent = "unrecognized";
    badge.className = "badge badge-warn";
    badge.title = "No known obfuscator fingerprint — generic cleanup applied.";
  }
}

function renderStats(r) {
  const outLen = (r.code || "").length;
  const t = r.timeMs != null ? `${r.timeMs} ms` : "";
  const errs = Array.isArray(r.errors) ? r.errors.length : 0;
  const parts = [];
  if (t) parts.push(t);
  parts.push(`${outLen.toLocaleString()} chars`);
  if (errs) parts.push(`${errs} note${errs > 1 ? "s" : ""}`);
  $("stats").textContent = parts.join("  ·  ");
  if (errs) $("stats").title = r.errors.map((x) => (typeof x === "string" ? x : x.message || JSON.stringify(x))).join("\n");
}

/* ---------------- status + buttons ---------------- */
function setStatus(html) { const s = $("status"); s.innerHTML = html; s.hidden = false; s.classList.remove("error"); }
function showError(text) { const s = $("status"); s.textContent = text; s.hidden = false; s.classList.add("error"); }
function hideStatus() { $("status").hidden = true; }
function setRunning(on) {
  const b = $("run");
  b.disabled = on;
  b.querySelector("span").textContent = on ? "Working…" : "Deobfuscate";
}

/* ---------------- controls ---------------- */
$("run").addEventListener("click", run);
document.addEventListener("keydown", (e) => {
  if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); run(); }
});

$("clear").addEventListener("click", () => {
  input.dispatch({ changes: { from: 0, to: input.state.doc.length, insert: "" } });
  setOutput("");
  hideStatus();
  $("detect").textContent = "no input"; $("detect").className = "badge badge-muted"; $("detect").title = "";
  $("stats").textContent = "";
});

const examples = $("examples");
for (const [id, s] of Object.entries(SAMPLES)) {
  const opt = document.createElement("option");
  opt.value = id; opt.textContent = s.label;
  examples.appendChild(opt);
}
examples.addEventListener("change", () => {
  const s = SAMPLES[examples.value];
  if (!s) return;
  input.dispatch({ changes: { from: 0, to: input.state.doc.length, insert: s.code } });
  examples.value = "";
  run();
});

$("file").addEventListener("change", async (e) => {
  const f = e.target.files && e.target.files[0];
  if (!f) return;
  const text = await f.text();
  input.dispatch({ changes: { from: 0, to: input.state.doc.length, insert: text } });
  e.target.value = "";
});

$("paste").addEventListener("click", async () => {
  try {
    const text = await navigator.clipboard.readText();
    input.dispatch({ changes: { from: 0, to: input.state.doc.length, insert: text } });
  } catch {
    showError("Clipboard access was blocked — paste with ⌘V / Ctrl+V instead.");
  }
});

$("copy").addEventListener("click", async () => {
  const text = output.state.doc.toString();
  if (!text) return;
  try { await navigator.clipboard.writeText(text); flash($("copy"), "Copied"); }
  catch { showError("Could not copy to clipboard."); }
});

$("download").addEventListener("click", () => {
  const text = output.state.doc.toString();
  if (!text) return;
  const blob = new Blob([text], { type: "text/javascript" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url; a.download = "deobfuscated.js"; a.click();
  URL.revokeObjectURL(url);
});

function flash(btn, label) {
  const old = btn.textContent; btn.textContent = label;
  setTimeout(() => (btn.textContent = old), 1200);
}

window.matchMedia("(prefers-color-scheme: dark)").addEventListener?.("change", () => {
  if (!localStorage.getItem("unspooler-theme")) applyTheme();
});
