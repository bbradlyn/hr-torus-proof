#!/usr/bin/env python3
"""gen-map.py -- the map from the HR paper's statements to the Lean declarations of HRTorus (T-0056, 2026-10-25).

Sources, and nothing else: papers/hr/main.aux (every \\newlabel of a theorem-like environment: number, title, page) and the
Lean sources under lean/HRTorus (every declaration whose docstring opens with a bold paper reference such as **Lemma 5.12(a)**,
the convention of the statement phases; for the first commit's modules, which predate that convention, the paper statements
their docstrings cite). Outputs: lean/MAP.md (the complete map), the appendix's LaTeX table, and a draft with the gaps.
Usage: gen-map.py <repo root> <MAP.md> <E-table.tex> <draft.md>"""
import re, sys, os
from collections import defaultdict, Counter
root, out_map, out_tex, out_draft = sys.argv[1:5]
aux = open(os.path.join(root, "papers/hr/main.aux")).read()
stmts = {}
def groups(text, i, n):
    """the next n brace groups of text starting at index i, with nested braces"""
    out = []
    for _ in range(n):
        while text[i] != "{": i += 1
        depth = 0; j = i
        while True:
            if text[j] == "{": depth += 1
            elif text[j] == "}":
                depth -= 1
                if depth == 0: break
            j += 1
        out.append(text[i + 1:j]); i = j + 1
    return out
labnum = {}  # label -> number, for Appendix C's label-named references (`Lemma C.theta` is `kz:lem:theta`)
for m in re.finditer(r"\\newlabel\{((?:kz:)?(thm|lem|prop|cor|def|ass|set|rem):[^}]*)\}\{", aux):
    num, page, title = groups(aux, m.end() - 1 + 1, 3)
    stmts[num] = (m.group(2), m.group(1), title, int(page)); labnum[m.group(1)] = num
KIND = {"thm": "Theorem", "lem": "Lemma", "prop": "Proposition", "cor": "Corollary", "def": "Definition", "ass": "Assumption", "set": "Setting", "rem": "Remark"}
LEAN = os.path.join(root, "lean/HRTorus")
def modname(path): return "HRTorus." + os.path.relpath(path, LEAN)[:-5].replace("/", ".")
def short(mod): return mod[len("HRTorus."):]
allmods = sorted(os.path.join(r, f) for r, _, fs in os.walk(LEAN) for f in fs if f.endswith(".lean") and "Axioms" not in f)
FIRST = ("IndexCore", "SlotFrame", "Laughlin")  # the first commit's modules: cited statements and curated main theorems, not labels
EXCLUDE = ("Fermion.Pilot.CAR",)  # the pilot's alternative representation of Lemma 5.1: not part of the correspondence (lean/README.md)
blockmods = [p for p in allmods if not any(short(modname(p)).startswith(x) for x in FIRST + EXCLUDE)]
firstmods = [p for p in allmods if any(short(modname(p)).startswith(x) for x in FIRST)]
decl = re.compile(r"/--\s*\*\*([^*]+)\*\*(.*?)-/\s*\n(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+(\S+)", re.S)
numre = re.compile(r"(Theorem|Lemma|Proposition|Corollary|Definition|Assumption|Setting|Remark)\s+([A-Z]\.\d+|\d+\.\d+)(.*)")
labre = re.compile(r"(Theorem|Lemma|Proposition|Corollary|Definition)\s+C\.([A-Za-z][A-Za-z0-9]*)(.*)")  # stage F: Appendix C by label name
KZ = {"Theorem": "thm", "Lemma": "lem", "Proposition": "prop", "Corollary": "cor", "Definition": "def"}
def part(p): return p.strip().lstrip(",").strip()
bynum = defaultdict(list); unmatched = []; total = 0
DEVNS = re.compile(r"^namespace (\w*Dev)\b.*?^end \1\b", re.S | re.M)  # proof devices: `…Dev` namespaces and `_dev`/`Dev` names are not statements of the paper
for path in blockmods:
    mod = modname(path); s = DEVNS.sub("", open(path).read())
    for m in decl.finditer(s):
        label, kind, name = m.group(1).strip(), m.group(3), m.group(4).split('.{')[0]
        if name.endswith(("_dev", "Dev")): continue
        total += 1
        nm = numre.match(label); nl = labre.match(label.replace("`", ""))
        if nm: bynum[nm.group(2)].append((mod, name, kind, part(nm.group(3))))
        elif nl and "kz:" + KZ[nl.group(1)] + ":" + nl.group(2) in labnum: bynum[labnum["kz:" + KZ[nl.group(1)] + ":" + nl.group(2)]].append((mod, name, kind, part(nl.group(3))))
        else: unmatched.append((mod, name, kind, label))
cite = re.compile(r"(Theorem|Lemma|Proposition|Corollary|Assumption|Definition|Setting)[~ ]+((?:A\.)?\d+\.\d+)")
corecites = defaultdict(Counter)   # num -> Counter(module)
for path in firstmods:
    mod = modname(path); s = open(path).read()
    if short(mod).startswith("Laughlin"): continue  # its docstrings cite the Laughlin paper
    for d in re.findall(r"/--(.*?)-/", s, flags=re.S):
        for c in cite.finditer(d): corecites[c.group(2)][mod] += 1
# the first commit's main theorems, from lean/README.md's descriptions (names verified to exist below)
MAIN = {"HRTorus.IndexCore.Main": ["index_core", "index_core_400"], "HRTorus.IndexCore.Translation": ["Orbital.translation_corollary", "Orbital.four_dvd_p", "Orbital.odd_plus", "Orbital.odd_minus"],
        "HRTorus.IndexCore.Ring": ["OrbitalRing.nonvacuity"], "HRTorus.SlotFrame.SlotFrame": ["localization_i", "localization_ii", "localization_iii", "localization"],
        "HRTorus.Laughlin.GramPoisson": ["fourier_g", "coset_poisson", "S_closed_form"]}
srcs = {modname(p): open(p).read() for p in allmods}
FIRST_STMTS = {  # statement -> [(module, [names], part)]; the first commit's modules carry no docstring labels, so these rows are curated and the names verified below
    "3.2": [("HRTorus.SlotFrame.SlotFrame", ["window_contDiff", "window_eq_zero", "window_sq_tsum"], "(i)"), ("HRTorus.SlotFrame.SlotFrame", ["consistency_ii", "Ia_nonempty"], "(ii)")],
    "3.5": [("HRTorus.SlotFrame.SlotFrame", ["localization_i", "localization_ii", "localization_iii", "localization"], "")],
    "6.18": [("HRTorus.IndexCore.Main", ["index_core", "index_core_400"], "finite-dimensional form, general U")],
    "7.2": [("HRTorus.IndexCore.Translation", ["Orbital.translation_corollary"], "finite content")],
    "7.3": [("HRTorus.IndexCore.Translation", ["Orbital.four_dvd_p"], "finite content")],
    "7.4": [("HRTorus.IndexCore.Translation", ["Orbital.odd_plus", "Orbital.odd_minus"], "finite content")],
}
UTHETA = {"6.11", "6.12", "6.13", "6.18"}  # formalized for U = Θ only
for mod, names in list(MAIN.items()) + [(m, ns) for rows in FIRST_STMTS.values() for m, ns, _ in rows]:
    for n in names:
        last = n.split(".")[-1]
        assert re.search(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|structure)\s+(?:[^\s.{(:]+\.)*" + re.escape(last) + r"\b", srcs[mod], flags=re.M), (mod, n)
def numkey(n):
    a, b = n.split("."); return (0 if a.isdigit() else 1, int(a) if a.isdigit() else a, int(b))
SPECIAL = {"2.10": "the lower bounds of (ii)–(iii) — at least ten zero modes at even `N`, at least two in each odd sector at odd `N ≥ 3` — are proved from Appendix C's explicit states (`ZeroModes.Lower`), which is all Theorem 8.1, Corollary 8.2 and Corollary 8.4 use; the exact counts and (i) are not formalized; the two `Assembly.Main` declarations are the bridges from the exact kernel dimensions to the named hypotheses `HasTenZeroModes`, `HasTwoZeroModes` of the reviewed statements",
           "2.8": "not formalized — left out at block A's statement review: the planar `V_1` units statement; no result of the paper and no Lean declaration depends on it"}
CNOTE = {  # Appendix C by label: what the stage-F modules (the lower bound of Theorem 2.10) leave out
    "kz:lem:A1": r"\emph{not formalized: not needed for the lower bound}", "kz:lem:A2": r"\emph{not formalized: not needed for the lower bound}",
    "kz:lem:A4": r"\emph{not formalized: not needed for the lower bound}",
    "kz:lem:A3": r" \emph{(the first identity; the norm identity not formalized)}",
    "kz:lem:A": r" \emph{((2) $\Rightarrow$ (3) and (3) $\Rightarrow$ (1); (1) $\Leftrightarrow$ (2) not formalized)}",
    "kz:lem:theta": r" \emph{((a), (c)--(f); (b) not formalized)}",
    "kz:def:G": r"\emph{not formalized as a definition; its conditions (i)--(iii) are proved for the explicit functions of Proposition~\ref{kz:prop:explicit} in \texttt{ZeroModes.Explicit}}",
    "kz:lem:B": r" \emph{((b), the numerators; (a), (c) and the surjectivity not formalized)}",
    "kz:lem:C": r"\emph{not formalized: the exact count}", "kz:lem:D": r"\emph{not formalized: the exact count}",
    "kz:prop:induct": r"\emph{not formalized: the exact count}", "kz:prop:base": r"\emph{not formalized: the exact count}",
    "kz:cor:bounds": r"\emph{not formalized: the exact count}",
    "kz:thm:T2": r" \emph{((ii)--(iii), the lower bounds: the existence of the two, resp.\ ten, independent zero modes; (i) and the exact counts not formalized)}",
}
# ---------- MAP.md
L = ["# The map from the HR paper's statements to the Lean declarations", "",
     "Generated by `lean/gen-map.py` from `papers/hr/main.aux` (after `papers/hr/build.sh`) and the Lean sources; do not edit by hand.",
     "A declaration appears under a statement when its docstring opens with that statement's number, or, for Appendix C, its label name",
     "(the convention of the modules written in the formalization's stages 1 and F); the first commit's modules (the index core, Lemma 3.5, the Laughlin pilot) predate the",
     "convention, and for them the map lists the statements their docstrings cite and their main theorems. Module names omit the",
     "`HRTorus.` prefix. Proof devices (declarations named with the suffix `_dev` or inside a `…Dev` namespace) are not listed. The paper's",
     "statement numbers are those of the version in `papers/hr/`.", "",
     "## By statement of the paper (Sections 2–8, Appendices B and C; Appendices A, D and the remarks only where cited)", ""]
rows_tex = []; covered = 0; counted = 0
def texname(n):
    rep = {"ν": r"\ensuremath{\nu}", "Θ": r"\ensuremath{\Theta}", "φ": r"\ensuremath{\varphi}", "δ": r"\ensuremath{\delta}"}
    bad = [c for c in n if ord(c) > 127 and c not in rep]
    assert not bad, (n, bad)
    for k, v in rep.items(): n = n.replace(k, v)
    return r"\texttt{" + n.replace("_", r"\_\allowbreak{}") + "}"
def texmod(m): return r"\texttt{" + short(m).replace("_", r"\_") + "}"
def textitle(t): return t.strip()  # LaTeX: the aux title verbatim (its \\cite commands render as in the paper)
def mdtitle(t): return re.sub(r"\\cite\s*(\[[^\]]*\])?\{([^}]*)\}", lambda mm: "[" + mm.group(2) + "]", t).replace("{", "").replace("}", "").strip()
for num in sorted(set(stmts) | set(bynum), key=numkey):
    kind, key, title, page = stmts.get(num, ("?", "?", "(no aux label)", 0)); sec = num.split(".")[0]
    ds = bynum.get(num, []); cc = corecites.get(num, Counter())
    if kind == "rem" and not ds: continue
    if sec in ("A", "D") and not ds and not cc: continue
    if kind != "rem": counted += 1
    if (ds or (cc and sec in ("6", "7", "A"))) and kind != "rem": covered += 1
    L.append(f"### {KIND.get(kind, kind)} {num} — {mdtitle(title)} (p. {page})"); L.append("")
    if num in SPECIAL: L.append(f"*{SPECIAL[num]}.*"); L.append("")
    bymod = defaultdict(list)
    for mod, name, k, part in ds: bymod[mod].append((name, k, part))
    for mod in sorted(bymod):
        L.append(f"- `{short(mod)}`: " + ", ".join(f"`{n}`" + (f" ({p})" if p else "") for n, k, p in bymod[mod]))
    for mod, names, part in FIRST_STMTS.get(num, []):
        L.append(f"- `{short(mod)}` (first commit): " + ", ".join(f"`{n}`" for n in names) + (f" — {part}" if part else ""))
    if cc and sec in ("6", "7", "A", "2", "4", "5"):
        L.append("- cited in the first commit's modules: " + ", ".join(f"`{short(m)}` ({c})" for m, c in cc.most_common()))
    if num in UTHETA: L.append("- the `Assembly` declarations are for `U = Θ` only")
    L.append("")
    # LaTeX row
    cell = []
    for mod in sorted(bymod):
        names = [n for n, k, p in bymod[mod]]
        shown = names[:4]; more = len(names) - len(shown)
        c = texmod(mod) + ": " + ", ".join(texname(n) for n in shown) + (f" and {more} more" if more else "")
        if num in UTHETA and short(mod).startswith("Assembly."): c += r" \emph{(for $U=\Theta$)}"
        cell.append(c)
    for mod, names, part in FIRST_STMTS.get(num, []):
        cell.append(texmod(mod) + ": " + ", ".join(texname(n) for n in names) + ((f" {part}" if part.startswith("(") else f" ({part})") if part else ""))
    if cc and sec in ("6", "7", "A") and not ds and num not in FIRST_STMTS:
        cell.append("index core: " + ", ".join(texmod(m) for m, c in cc.most_common(3)))
    elif cc and sec in ("6", "7", "A") and num not in FIRST_STMTS:
        cell.append("index core: " + ", ".join(texmod(m) for m, c in cc.most_common(2)))
    note = ""
    if num == "2.10": note = r" \emph{(the lower bounds of (ii)--(iii), all the main theorems use; the exact counts and (i) not formalized)}"
    if sec == "C": note = CNOTE.get(stmts[num][1], "") if num in stmts else ""
    if num == "2.8": note = r"\emph{not formalized: the planar units statement; nothing in the formalization depends on it}"
    rows_tex.append(f"{KIND.get(kind, kind)}~{num} & {textitle(title)} & " + ("; ".join(cell) + note if cell else note) + r" \\")
L += ["## Labelled declarations that match no statement number", ""]
for mod, name, k, label in unmatched: L.append(f"- `{short(mod)}` · `{name}`: **{label}**")
L += ["", "## The first commit's modules: main theorems and the statements their docstrings cite", "", "`Fermion.Pilot.CAR`, the pilot's alternative representation of Lemma 5.1, is not part of the correspondence (see `lean/README.md`).", ""]
for path in firstmods:
    mod = modname(path); s = srcs[mod]
    cited = Counter()
    for d in re.findall(r"/--(.*?)-/", s, flags=re.S):
        for c in cite.finditer(d): cited[c.group(1) + " " + c.group(2)] += 1
    line = f"- `{short(mod)}`"
    if mod in MAIN: line += ": " + ", ".join(f"`{n}`" for n in MAIN[mod])
    if cited and not short(mod).startswith("Laughlin"): line += " — cites " + ", ".join(f"{k} ({v})" for k, v in sorted(cited.items(), key=lambda kv: numkey(kv[0].split()[-1].replace('A.', '0.') if False else kv[0].split()[-1])))
    L.append(line)
L += ["", f"## Counts", "", f"- Numbered statements of Sections 2–8 and Appendices B–C: {counted}; with a Lean declaration labelled by their number or name or proved in the index core: {covered}.",
      f"- Labelled declarations in the stage-1 and stage-F modules: {total} ({sum(len(v) for v in bynum.values())} under a statement number, {len(unmatched)} named after what they are).", ""]
open(out_map, "w").write("\n".join(L))
# ---------- LaTeX table
T = [r"% generated by lean/gen-map.py from papers/hr/main.aux and the Lean sources; do not edit by hand",
     r"\begin{footnotesize}", r"\begin{longtable}{@{}p{2.35cm}p{3.35cm}>{\raggedright\arraybackslash}p{9.6cm}@{}}",
     r"\toprule Statement & Title & Lean module: declarations \\ \midrule \endfirsthead",
     r"\toprule Statement & Title & Lean module: declarations \\ \midrule \endhead", r"\bottomrule \endlastfoot"] + rows_tex + [r"\end{longtable}", r"\end{footnotesize}"]
open(out_tex, "w").write("\n".join(T) + "\n")
open(out_draft, "w").write("---\nowner: Claude Fable 5.1 (T-0056's coordinator); generated by work/appendix/gen-map.py — regenerate, never edit\npurpose: the run log of the map generator — the paper statements without a labelled Lean declaration and the labels that match no statement, behind lean/MAP.md and the appendix table\ncreated: 2026-10-25\nexpires: regenerated at every change; superseded by lean/MAP.md once the appendix is committed\nlinks: [T-0056]\n---\n\n# gen-map.py run\n\n"
    + f"labelled declarations {total}; statements counted {counted}; covered {covered}; unmatched labels {len(unmatched)}\n\n## Statements with neither a labelled declaration nor a core citation\n\n"
    + "\n".join(f"- {KIND.get(stmts[n][0], '?')} {n}: {mdtitle(stmts[n][2])}" for n in sorted(stmts, key=numkey) if n not in bynum and n not in corecites and stmts[n][0] != "rem" and n.split('.')[0] not in ('A', 'C', 'D')) + "\n")
print(f"labelled {total}; statements {counted}; covered {covered}; unmatched {len(unmatched)}; table rows {len(rows_tex)}")
