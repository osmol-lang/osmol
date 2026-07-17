#!/usr/bin/env python3
# ====================================================================
#  OSMOL v0.1 — reference interpreter (Phase 3)
#
#  There is no send.
#  (grep this file: the word appears only in the tombstone list.)
#
#  Implements the runnable core of the Osmol v0.1 spec:
#    twin / hold / seek / owe / decide / express
#    membrane { selector -> party [when c]: transform }
#    attention { interrupts n/period, quiet a-b, threshold party x }
#    bond party { trust level }
#
#  Engine (Spec section 6):
#    P(A->B,k,g) = R * U * T * M  -  C ;  flow iff P > theta_B(A)
#    Absorption is monotone: a flow closes exactly one gap.
#    Theorem 1 (machine-checked in osmol_convergence.v) therefore
#    guarantees this loop terminates in <= initial gapcount flows.
#    The engine asserts that bound at runtime.
#
#  v0.1 interpreter pragmas (documented simplifications):
#    - circles: a sender's membrane audience 'family'/'team' matches
#      any party the sender bonds with trust high; 'others' = the rest.
#    - wall-clock is not simulated: deadlines raise urgency (U=1.3)
#      and drive escalation notes, but 'quiet' hours are stored only.
#    - owe X(args) auto-emits: hold status(args.X) = in-progress
#      (commitments generate structural supply; Spec section 3).
#    - decide requires human judgment: the engine cannot choose.
#      Resolutions are injected via --resolve twin:fact=value.
#    - placement: express -> human-lane; escalate-gaps -> ledger;
#      everything else -> silent. Interrupts exist but demand a
#      passed 'escalate' deadline, which needs wall-clock: unused.
# ====================================================================

import argparse
import re
import sys

TOMBSTONES = {"send", "notify", "broadcast", "blast",
              "cc", "bcc", "forward", "reply"}

DEFAULT_THETA = {"family": 0.3, "team": 0.4, "others": 0.8}
TRUST_T = {"high": 1.0, "medium": 0.6, "low": 0.3}
CAST_M = {"exact": 1.0, "category": 0.5, "existence": 0.3, "deny": 0.0}


class OsmolError(Exception):
    pass


# ---------------------------------------------------------------- model

class Twin:
    def __init__(self, name):
        self.name = name
        self.holds = {}        # fact -> value
        self.gaps = {}         # fact -> {"by":..., "esc":...}
        self.owes = []         # (fact, to, by)
        self.decides = {}      # fact -> {"among":[...], "by":...}
        self.membrane = []     # (selector, party, cond, transform)
        self.attention = {"interrupts": None, "quiet": None,
                          "theta": {}}
        self.bonds = {}        # party -> trust
        self.expressions = []  # (to, text)
        self.ledger = []
        self.lane = []         # human lane, verbatim


class Mesh:
    def __init__(self):
        self.twins = {}

    def gapcount(self):
        return sum(len(t.gaps) for t in self.twins.values())


# ---------------------------------------------------------------- parse

RX = {
    "twin":    re.compile(r'^twin\s+([\w.-]+)\s*\{$'),
    "hold":    re.compile(r'^hold\s+(?P<fact>[\w.-]+\([^)]*\))\s*=\s*'
                          r'(?P<val>[^,]+?)'
                          r'(?:\s*,\s*(?P<tk>decays|until)\s+(?P<tv>\S+))?$'),
    "seek":    re.compile(r'^seek\s+(?P<fact>[\w.-]+\([^)]*\))'
                          r'(?:\s+by\s+(?P<by>\S+))?'
                          r'(?:\s+else\s+(?P<esc>escalate|sync|drop))?$'),
    "owe":     re.compile(r'^owe\s+(?P<fact>[\w.-]+\([^)]*\))\s+to\s+'
                          r'(?P<to>[\w-]+)(?:\s+by\s+(?P<by>\S+))?$'),
    "decide":  re.compile(r'^decide\s+(?P<fact>[\w.-]+\([^)]*\))\s+among\s*'
                          r'\{(?P<opts>[^}]*)\}(?:\s+by\s+(?P<by>\S+))?$'),
    "express": re.compile(r'^express\s+to\s+(?P<to>[\w-]+)\s*:\s*'
                          r'"(?P<text>.*)"$'),
    "bond":    re.compile(r'^bond\s+(?P<who>[\w-]+)\s*\{\s*trust\s+'
                          r'(?P<lv>\w+)\s*\}$'),
    "mrule":   re.compile(r'^(?P<sel>[\w.*-]+\([^)]*\)|[\w.*-]+)\s*->\s*'
                          r'(?P<party>@role\([^)]*\)|[\w-]+)'
                          r'(?:\s+when\s+(?P<cond>[\w-]+))?\s*:\s*'
                          r'(?P<tr>exact|coarse\([^)]+\)|category|'
                          r'existence|deny)$'),
    "a_int":   re.compile(r'^interrupts\s+(\d+)\s*/\s*(\w+)$'),
    "a_quiet": re.compile(r'^quiet\s+(\S+)$'),
    "a_theta": re.compile(r'^threshold\s+([\w-]+)\s+([\d.]+)$'),
}


def strip_comment(line):
    return line.split("--", 1)[0].rstrip()


def tombstone_check(line, lineno):
    bare = re.sub(r'"[^"]*"', '', line)          # strings are payload
    for tok in re.findall(r'[A-Za-z]+', bare):
        if tok.lower() in TOMBSTONES:
            raise OsmolError(
                f"line {lineno}: error[O-000]: '{tok}' — there is no "
                f"{tok}. Declare what you hold; declare what you seek; "
                f"the mesh does the rest.")


def parse(src):
    mesh = Mesh()
    twin, sub = None, None
    for n, raw in enumerate(src.splitlines(), 1):
        line = strip_comment(raw).strip()
        if not line:
            continue
        tombstone_check(line, n)

        if twin is None:
            m = RX["twin"].match(line)
            if m:
                twin = Twin(m.group(1))
                mesh.twins[twin.name] = twin
                continue
            raise OsmolError(f"line {n}: expected 'twin <name> {{'")

        if sub == "membrane":
            if line == "}":
                sub = None
                continue
            m = RX["mrule"].match(line)
            if not m:
                raise OsmolError(f"line {n}: bad membrane rule")
            twin.membrane.append((m["sel"], m["party"],
                                  m["cond"], m["tr"]))
            continue

        if sub == "attention":
            if line == "}":
                sub = None
                continue
            if RX["a_int"].match(line):
                g = RX["a_int"].match(line)
                twin.attention["interrupts"] = (int(g.group(1)),
                                                g.group(2))
            elif RX["a_quiet"].match(line):
                twin.attention["quiet"] = RX["a_quiet"].match(line).group(1)
            elif RX["a_theta"].match(line):
                g = RX["a_theta"].match(line)
                twin.attention["theta"][g.group(1)] = float(g.group(2))
            else:
                raise OsmolError(f"line {n}: bad attention rule")
            continue

        if line == "membrane {":
            sub = "membrane"
            continue
        if line == "attention {":
            sub = "attention"
            continue
        if line == "}":
            twin = None
            continue

        for kind in ("hold", "seek", "owe", "decide", "express", "bond"):
            m = RX[kind].match(line)
            if not m:
                continue
            d = m.groupdict()
            if kind == "hold":
                twin.holds[d["fact"]] = d["val"].strip()
            elif kind == "seek":
                twin.gaps[d["fact"]] = {"by": d["by"], "esc": d["esc"]}
            elif kind == "owe":
                twin.owes.append((d["fact"], d["to"], d["by"]))
                fm = re.match(r'([\w.-]+)\(([^)]*)\)', d["fact"])
                sf = (f"status({fm.group(2)}.{fm.group(1)})"
                      if fm and fm.group(2) else f"status({d['fact']})")
                twin.holds.setdefault(sf, "in-progress")
            elif kind == "decide":
                twin.decides[d["fact"]] = {
                    "among": [o.strip() for o in d["opts"].split(",")],
                    "by": d["by"]}
            elif kind == "express":
                twin.expressions.append((d["to"], d["text"]))
            elif kind == "bond":
                twin.bonds[d["who"]] = d["lv"]
            break
        else:
            raise OsmolError(f"line {n}: unrecognized declaration: "
                             f"{line!r}")
    return mesh


# --------------------------------------------------------------- engine

def sel_match(selector, fact):
    if "(" not in selector:
        selector += "(*)"
    rx = re.escape(selector).replace(r"\*", ".*")
    return re.fullmatch(rx, fact) is not None


def audience_match(sender, party, receiver):
    if party in ("all",):
        return True
    if party in ("family", "team"):
        return sender.bonds.get(receiver) == "high"
    if party == "others":
        return sender.bonds.get(receiver) != "high"
    return party == receiver


def membrane_cast(sender, fact, receiver):
    for sel, party, cond, tr in sender.membrane:
        if sel_match(sel, fact) and audience_match(sender, party,
                                                   receiver):
            return tr
    return None                                   # no rule: no flow


def cast_weight(tr):
    if tr is None:
        return 0.0
    if tr.startswith("coarse"):
        return 0.7
    return CAST_M[tr]


def theta_for(receiver, sender):
    cls = ("family" if receiver.bonds.get(sender) == "high" else "others")
    return receiver.attention["theta"].get(
        cls, DEFAULT_THETA[cls]), cls


def pressure(sender, receiver, fact, gap, tr):
    R = 1.0
    U = 1.3 if gap["by"] else 1.0
    T = TRUST_T.get(receiver.bonds.get(sender.name, "medium"), 0.6)
    M = cast_weight(tr)
    C = 0.0
    return R * U * T * M - C, (R, U, T, M)


def apply_cast(value, tr):
    if tr == "exact":
        return value
    if tr.startswith("coarse"):
        return f"~{value} [{tr}]"
    if tr == "category":
        return f"{value} [class-level]"
    if tr == "existence":
        return "[exists]"
    return None


def settle(mesh, resolutions, out=print):
    # human judgments arrive as declarations, never as choices the
    # machine makes on a person's behalf
    pending_notes = []
    for spec in resolutions:
        who, rest = spec.split(":", 1)
        fact, val = rest.split("=", 1)
        t = mesh.twins[who]
        if fact in t.decides:
            if val not in t.decides[fact]["among"]:
                raise OsmolError(f"resolution {val!r} not among options "
                                 f"for {fact}")
            del t.decides[fact]
            t.holds[fact] = val
            pending_notes.append(
                f"  [human judgment] {who} resolves {fact} = {val}")

    g0 = mesh.gapcount()
    out(f"initial gapcount: {g0}   "
        f"(Theorem 1 bound: equilibrium in <= {g0} flows)")
    for note in pending_notes:
        out(note)

    # the human lane delivers first, verbatim, provenance-labeled
    for t in mesh.twins.values():
        for to, text in t.expressions:
            if to in mesh.twins:
                mesh.twins[to].lane.append((t.name, text))
                out(f'  human-lane  {t.name} -> {to}  (verbatim, '
                    f'provenance=human): "{text}"')

    flows = 0
    while True:
        best = None
        for b in mesh.twins.values():
            for fact, gap in b.gaps.items():
                for a in mesh.twins.values():
                    if a is b or fact not in a.holds:
                        continue
                    tr = membrane_cast(a, fact, b.name)
                    if tr in (None, "deny"):
                        continue
                    th, cls = theta_for(b, a.name)
                    P, parts = pressure(a, b, fact, gap, tr)
                    if P > th and (best is None or P > best[0]):
                        best = (P, parts, th, cls, a, b, fact, gap, tr)
        if best is None:
            break
        P, (R, U, T, M), th, cls, a, b, fact, gap, tr = best
        flows += 1
        assert flows <= g0, "Theorem 1 violated — impossible"
        val = apply_cast(a.holds[fact], tr)
        b.holds[fact] = val
        esc = b.gaps.pop(fact)["esc"]
        place = "ledger" if esc == "escalate" else "silent"
        if place == "ledger":
            b.ledger.append(f"{fact} = {val}")
        out(f"t{flows}  {a.name}.{fact} --{tr}--> {b.name}   "
            f"P={P:.2f} (R{R:.1f}*U{U:.1f}*T{T:.1f}*M{M:.1f}) "
            f"> theta[{cls}]={th}   [{place}]")

    out("")
    out(f"EQUILIBRIUM after {flows} flows "
        f"(Theorem 1 bound {g0}: respected)")
    out(f"messages composed by humans: 0 "
        f"(the grammar has no verb for it)")
    out(f"interruptions: 0")
    for t in mesh.twins.values():
        if t.ledger:
            out(f"ledger[{t.name}]: " + "; ".join(t.ledger))
    open_gaps = mesh.gapcount()
    for t in mesh.twins.values():
        for fact, gap in t.gaps.items():
            note = (" -> sync will be scheduled (else sync)"
                    if gap["esc"] == "sync" else "")
            out(f"open gap [{t.name}]: {fact}{note}")
        for fact, d in t.decides.items():
            out(f"awaiting human judgment [{t.name}]: {fact} among "
                f"{d['among']}  (machines do not choose venues)")
    if open_gaps == 0 and all(not t.decides for t in mesh.twins.values()):
        out("open gaps: 0 — silence is a fixpoint")
    return flows


# ----------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description="Osmol v0.1 reference "
                                             "interpreter")
    ap.add_argument("file")
    ap.add_argument("--resolve", action="append", default=[],
                    metavar="twin:fact=value",
                    help="inject a human judgment for a pending decide")
    args = ap.parse_args()

    print("OSMOL v0.1 - reference interpreter")
    try:
        src = open(args.file, encoding="utf-8").read()
        mesh = parse(src)
        print(f"parsed {args.file}: {len(mesh.twins)} twins, "
              f"0 sends (no such construct exists)")
        settle(mesh, args.resolve)
    except OsmolError as e:
        print(f"osmol: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
