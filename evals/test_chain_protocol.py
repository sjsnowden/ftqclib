"""Goal: protocol v2 spends retrieval only on new, literal, snapshot-bound evidence.

Method: finite backend observations test grammar, owner quoting, batched effects,
cached initial declarations, budget reservations and failures. Formal text remains
verbatim while prompt metadata shrinks. No model, compiler, network or subprocess runs.
"""
import json

import chain_protocol as protocol

SNAPSHOT = "a" * 64
RECEIPT = "b" * 64
FORMALISM = {"schema": 1, "modules": ["Library.Base"], "anchors": [], "semantic_notes": []}


def request(kind="check_candidate", **changes):
    value = {"action": kind, "proof": "by\n  rfl" if kind == "check_candidate" else None,
             "names": ["Library.fact"] if kind == "read_declarations" else None,
             "query": "cosetLeader" if kind == "search_name" else None,
             "reason": "missing prerequisite" if kind == "blocked" else None}
    return json.dumps({**value, **changes})


def field(text, truncated=False):
    return {"text": text, "truncated": truncated, "bytes": len(text.encode()) + (50 if truncated else 0),
            "retained_bytes": len(text.encode())}


def declaration(name="Library.fact", *, kind="theorem", **changes):
    return {"status": "ok", "name": name.split("."), "display_name": name, "kind": kind,
            "type": field("∀ x : Nat, x = x"), "body": field("fun x => x") if kind == "definition" else None,
            "docstring": field("Explanatory documentation not needed for the formal obligation."),
            "origin_module": ["Library", "Base"], "snapshot": SNAPSHOT, "receipt": RECEIPT,
            "advisory": True, "cache_hit": False, **changes}


def search(*names, **changes):
    return {"status": "ok" if names else "empty", "hits": [
        {"name": name, "module": "Library.Base", "type": field("True")} for name in names],
        "count": len(names), "hits_truncated": False, "snapshot": SNAPSHOT, "receipt": RECEIPT, **changes}


class Backend:
    def __init__(self, responses=()):
        self.responses, self.calls = list(responses), []
        self.session = None

    def call(self, operation, payload):
        if self.session is not None:
            assert self.session.requests_used == len(self.calls) + 1, "reservation must precede effect"
        self.calls.append((operation, payload))
        response = self.responses.pop(0)
        if isinstance(response, OSError):
            raise response
        return response


def session(responses=(), *, budget=8, initial=()):
    backend = Backend(responses)
    owner = protocol.Session(backend, budget, SNAPSHOT, initial=initial)
    backend.session = owner
    return owner, backend


def grammar():
    for raw in [request(), request("blocked"), request("read_declarations"), request("search_name"),
                request("read_declarations", names=["Ω.lemma₁'", "_root_.Library.fact"]),
                request("search_name", query="Ω" * 120)]:
        assert protocol.action(raw)[1] is None
    bad = [request("search_name", query=query) for query in [
        "find a coset leader", '"cosetLeader"', "_ + _ = _", "Nat, _ → _", "--help", "../answers",
        "Library..fact", "Library.", ".Library", "file:/answer", "a\\b", "$(id)", "x;bash",
        "a\nb", "a\tb", "123", "'name", "a\x00b", "Ω" * 121, "\ud800"]]
    bad += [request("read_declarations", names=names) for names in [
        None, "Library.fact", [], ["A"] * 5, ["A", "A"], ["Library fact"], ["A/B"],
        ["A", 4], ["x" * 257], ["Ω" * 129], ["«quoted name»"]]]
    bad += [request("search"), request("read_declaration"), request("bash"), request(command="git diff"),
            request(query="inactive"), request(proof="by\x00"), request(proof="x" * 16385),
            request().replace('"action":', '"action":"search_name","action":'), "[]", "null", "{",
            '{"action":NaN}', "[" * 2000, "x" * 131073]
    owner, backend = session()
    for raw in bad:
        assert owner.dispatch(raw)["status"] == "refused", raw[:100]
    assert not backend.calls and owner.requests_used == 0
    assert owner.ineffective_requests == len(bad)


def effects():
    owner, backend = session([search("Library.cosetLeader")])
    result = owner.dispatch(request("search_name"))
    assert result["status"] == "retrieval_result"
    assert backend.calls == [("search", '"cosetLeader"')]
    assert result["receipts"] == [RECEIPT] and result["responses"][0]["snapshot"] == SNAPSHOT
    assert owner.dispatch(request("search_name"))["status"] == "refused"
    assert len(backend.calls) == 1 and owner.requests_used == 1 and owner.ineffective_requests == 1
    owner, backend = session([search("Ω.lemma₁'")])
    assert owner.dispatch(request("search_name", query="Ω.lemma₁'"))["status"] == "retrieval_result"
    assert backend.calls == [("search", json.dumps("Ω.lemma₁'", ensure_ascii=False))]
    names = ["Library.one", "Library.two", "Ω.lemma₁'", "Library.four"]
    owner, backend = session([declaration(name) for name in names], budget=4)
    result = owner.dispatch(request("read_declarations", names=names))
    assert result["status"] == "retrieval_result" and len(result["responses"]) == 4
    assert backend.calls == [("read_declaration", name.split(".")) for name in names]
    assert owner.requests_left == 0 and len(owner.retrieved["evidence"]) == 4
    assert owner.dispatch(request())["status"] == "candidate"
    assert owner.dispatch(request("blocked"))["status"] == "blocked"
    assert owner.dispatch(request("read_declarations", names=["New.fact"]))["status"] == "refused"
    assert len(backend.calls) == 4


def supplied():
    initial = declaration()
    owner, backend = session(initial=[initial, initial])
    assert len(owner.initial) == 1
    result = owner.dispatch(request("read_declarations"))
    assert result["status"] == "refused" and result["ineffective"]
    assert not backend.calls and owner.requests_used == 0
    owner, backend = session([declaration("New.fact")], initial=[initial], budget=1)
    result = owner.dispatch(request("read_declarations", names=["Library.fact", "New.fact"]))
    assert result["status"] == "retrieval_result" and len(backend.calls) == 1
    assert backend.calls[0] == ("read_declaration", ["New", "fact"])
    owner, backend = session([search("Library.fact"), search()], initial=[initial])
    assert owner.dispatch(request("search_name", query="fact"))["status"] == "refused"
    assert owner.dispatch(request("search_name", query="unfindable"))["status"] == "refused"
    assert owner.requests_used == 2 and owner.ineffective_requests == 2
    owner, backend = session([{"status": "missing", "name": ["Absent"], "receipt": RECEIPT, "snapshot": SNAPSHOT}])
    assert owner.dispatch(request("read_declarations", names=["Absent"]))["status"] == "refused"
    assert owner.dispatch(request("read_declarations", names=["Absent"]))["status"] == "refused"
    assert len(backend.calls) == 1


def failures():
    owner, backend = session(budget=1)
    assert owner.dispatch(request("read_declarations", names=["A", "B"]))["status"] == "refused"
    assert not backend.calls and owner.requests_used == 0
    cases = [OSError("unavailable"), declaration(snapshot="c" * 64), declaration(receipt="invalid"),
             declaration("Different.name"), declaration(type={"text": "True"}),
             {"status": "error", "reason": "query failed", "receipt": RECEIPT, "snapshot": SNAPSHOT}]
    for response in cases:
        owner, backend = session([response], budget=2)
        result = owner.dispatch(request("read_declarations"))
        assert result["status"] == "retrieval_failed" and owner.requests_used == 1
        if not isinstance(response, OSError):
            assert result["responses"] == [response], "bounded refused raw response was lost"
        assert owner.dispatch(request("read_declarations"))["status"] == "refused"
        assert len(backend.calls) == 1 and owner.requests_left == 1
    owner, backend = session([search(status="invalid_query", reason="error query")])
    assert owner.dispatch(request("search_name"))["status"] == "retrieval_failed"
    assert owner.requests_used == 1 and owner.ineffective_requests == 1
    for initial in [[declaration(snapshot="c" * 64)], [declaration(), declaration(type=field("False"))]]:
        try:
            session(initial=initial)
        except ValueError:
            pass
        else:
            raise AssertionError("stale or contradictory initial evidence admitted")


def cumulative():
    owner, backend = session([declaration("A"), search("B", "A"), declaration("B", kind="definition"), declaration("C")])
    for kind, fields in [("read_declarations", {"names": ["A"]}), ("search_name", {"query": "B"}),
                         ("read_declarations", {"names": ["B"]}), ("read_declarations", {"names": ["C"]})]:
        assert owner.dispatch(request(kind, **fields))["status"] == "retrieval_result"
    evidence = owner.retrieved["evidence"]
    assert [row["name"] for row in evidence] == ["A", "B", "C"]
    assert evidence[1]["kind"] == "definition" and evidence[1]["body"]["text"] == "fun x => x"
    prior = json.dumps(owner.retrieved)
    duplicate = owner.dispatch(request("read_declarations", names=["A", "B"]))
    assert duplicate["status"] == "refused" and duplicate["supplied_names"] == ["A", "B"]
    assert "retained evidence" in duplicate["reason"] and len(backend.calls) == 4
    assert json.dumps(owner.retrieved) == prior and owner.ineffective_requests == 1
    assert owner.dispatch(request())["status"] == "candidate"
    packet = protocol.packet({"obligation": "True"}, FORMALISM, SNAPSHOT, requests_left=owner.requests_left,
                             retrieved={"initial": owner.initial, "retained": owner.retrieved})
    assert [row["name"] for row in packet["retrieved"]["retained"]["evidence"]] == ["A", "B", "C"]


def projection():
    original = declaration(kind="definition", type=field("∀ x : Nat, " + "x = x " * 500),
                           body=field("fun x => " + "x " * 1500, True), docstring=field("omit me" * 500))
    raw = json.dumps(original, ensure_ascii=False)
    projected = protocol.compact(original)
    assert projected["type"] == {"text": original["type"]["text"], "truncated": False}
    assert projected["body"] == {"text": original["body"]["text"], "truncated": True}
    assert set(projected) == {"status", "name", "kind", "type", "body"}
    assert json.dumps(original, ensure_ascii=False) == raw, "projection mutated the raw retained observation"
    assert len(json.dumps(projected)) < len(raw)
    hits = protocol.compact(search("Library.fact", hits_truncated=True, count=9))
    assert hits["hits_truncated"] and hits["count"] == 9
    assert set(hits["hits"][0]) == {"name", "type"}
    packet = protocol.packet({"obligation": "True"}, FORMALISM, SNAPSHOT, requests_left=1,
                             retrieved={"initial": [projected], "latest": None})
    assert packet["schema"] == 2 and packet["snapshot"] == SNAPSHOT
    assert packet["capabilities"] == ["check_candidate", "blocked", "read_declarations", "search_name"]
    assert "proof/names/query/reason" in packet["protocol"]
    huge = declaration(type=field("x" * 33000))
    try:
        protocol.compact(huge)
    except ValueError:
        pass
    else:
        raise AssertionError("oversized evidence was silently clipped")
    rows = [declaration(name, type=field("x" * 17000)) for name in ("A", "B")]
    owner, backend = session(rows)
    refused = owner.dispatch(request("read_declarations", names=["A", "B"]))
    assert refused["status"] == "retrieval_failed" and owner.retrieved is None
    assert len(refused["responses"]) == 2 and len(backend.calls) == 2
    owner, backend = session([rows[1]], initial=[rows[0]])
    refused = owner.dispatch(request("read_declarations", names=["B"]))
    assert refused["status"] == "retrieval_failed" and owner.retrieved is None and len(backend.calls) == 1


def check():
    grammar()
    effects()
    supplied()
    failures()
    cumulative()
    projection()
    print("Protocol v2: literal retrieval, batches, supplied-evidence cache, futility, budgets and compact evidence passed")


if __name__ == "__main__":
    check()
