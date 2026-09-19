#!/usr/bin/env python3
"""Memory probe for a Lean file.

usage: memprobe.py SRC.lean OUT_DIR [--cap 4G] [--timeout 1800] [--async]

Run from the project root (so that `lake env` picks the project's toolchain).  Written to track
down the out-of-memory compile of GateNext.lean (Sept 2026): the culprits were `omega` on nested
`min`s and a 52-case proof held in one declaration; see gen_gatenext.py.

* copies SRC into OUT_DIR/probe.lean, inserting before every top-level declaration a
  `#eval` that appends "<label> <mono ms> <VmRSS kB>" to OUT_DIR/ckpt.log (streamed: a
  killed run still shows how far it got);
* runs `lake env lean` on it inside a systemd user scope with MemoryMax=cap (no swap);
* samples the RSS of the Lean process every 100 ms into OUT_DIR/rss.log;
* prints the checkpoints with the time and memory spent until the next one.
"""
import os, re, subprocess, sys, time, psutil

src, out = sys.argv[1], sys.argv[2]
cap = "4G"; timeout = 1800; use_async = False
args = sys.argv[3:]
i = 0
while i < len(args):
    if args[i] == "--cap": cap = args[i + 1]; i += 2
    elif args[i] == "--timeout": timeout = int(args[i + 1]); i += 2
    elif args[i] == "--async": use_async = True; i += 1
    else: raise SystemExit(f"unknown arg {args[i]}")
os.makedirs(out, exist_ok=True)
ckpt = os.path.join(out, "ckpt.log")
open(ckpt, "w").close()

lines = open(src).read().split("\n")
START = re.compile(r"^(theorem|def|abbrev|structure|instance|def_module|seal|@\[|/--|section|end |variable|include|#eval|#print|#check)")
NAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|def|abbrev|structure|instance|def_module)\s+([^\s:({\[]+)")

def ckpt_cmd(label):
    return ("#eval show IO Unit from do\n"
            "  let st ← IO.FS.readFile \"/proc/self/status\"\n"
            "  let rss := ((st.splitOn \"\\n\").find? (·.startsWith \"VmRSS\")).getD \"VmRSS: ?\"\n"
            f"  IO.FS.withFile \"{ckpt}\" .append fun h => do h.putStrLn s!\"{label} {{← IO.monoMsNow}} {{rss}}\"; h.flush")

res = []
in_block_comment = False   # inside /- ... -/ or /-- ... -/
prefix_pending = False     # a docstring, attribute line or `seal .. in` awaits its declaration
header_done = False
for ln, line in enumerate(lines, 1):
    stripped = line.rstrip()
    if not header_done and stripped.startswith("namespace"):
        res.append(line)
        if not use_async:
            res.append("set_option Elab.async false")
        res.append(ckpt_cmd("L%d:namespace" % ln))
        header_done = True
        continue
    if in_block_comment:
        res.append(line)
        if "-/" in stripped:
            in_block_comment = False
        continue
    if header_done and START.match(stripped) and not prefix_pending:
        # label with the name of the declaration that follows
        label = None
        for j in range(ln - 1, min(ln + 12, len(lines))):
            m = NAME.match(lines[j])
            if m: label = m.group(1); break
        res.append(ckpt_cmd("L%d:%s" % (ln, label or stripped.split()[0])))
    res.append(line)
    if stripped.startswith("/-"):
        prefix_pending = stripped.startswith("/--")
        if "-/" not in stripped[2:]:
            in_block_comment = True
    elif stripped.startswith("@[") and stripped.endswith("]"):
        prefix_pending = True
    elif (stripped.startswith("seal ") or stripped.startswith("set_option ")) and stripped.endswith(" in"):
        prefix_pending = True
    elif stripped and not stripped.startswith(" ") and not stripped.startswith("--"):
        prefix_pending = False
res_text = "\n".join(res)
# the last checkpoint marks the end of the file
res_text += "\n" + ckpt_cmd("EOF") + "\n"
probe = os.path.join(out, "probe.lean")
open(probe, "w").write(res_text)

cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={cap}", "-p", "MemorySwapMax=0",
       "timeout", str(timeout), "lake", "env", "lean", probe]
t0 = time.monotonic()
log = open(os.path.join(out, "lean.out"), "w")
p = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, cwd=os.getcwd())
rss_log = open(os.path.join(out, "rss.log"), "w")
peak = 0
while p.poll() is None:
    try:
        tot = 0
        for c in psutil.Process(p.pid).children(recursive=True):
            if c.name() == "lean":
                tot += c.memory_info().rss
        peak = max(peak, tot)
        rss_log.write(f"{int(time.monotonic()*1000)} {tot//2**20}\n"); rss_log.flush()
    except psutil.Error:
        pass
    time.sleep(0.1)
t1 = time.monotonic()
log.close(); rss_log.close()
print(f"exit={p.returncode} wall={t1-t0:.1f}s peakRSS={peak/2**30:.2f}GB cap={cap}")

rows = []
for l in open(ckpt):
    parts = l.split()
    if len(parts) >= 3:
        rows.append((parts[0], int(parts[1]), int(parts[3]) if len(parts) > 3 and parts[3].isdigit() else -1))
end_ms = int(t1 * 1000)
print(f"{'checkpoint':40s} {'dt(s)':>8s} {'RSS@ckpt(MB)':>13s} {'peak until next(MB)':>20s}")
samples = [tuple(map(int, l.split())) for l in open(os.path.join(out, "rss.log")) if l.strip()]
for k, (lab, ms, rss) in enumerate(rows):
    nxt = rows[k + 1][1] if k + 1 < len(rows) else end_ms
    seg = [m for (t, m) in samples if ms <= t <= nxt]
    pk = max(seg) if seg else -1
    print(f"{lab:40s} {(nxt-ms)/1000:8.1f} {rss//1024:13d} {pk:20d}")
if rows and rows[-1][0] != "EOF":
    print("*** stopped after the last checkpoint above (killed, timed out or errored) ***")
print("--- lean output (errors) ---")
os.system(f"grep -v '^warning' {os.path.join(out, 'lean.out')} | grep -B1 -A6 'error' | head -40")
