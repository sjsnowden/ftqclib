"""Goal: typed retrieval cannot acquire path/shell authority or bypass a shared budget.

Method: scripted actions and injected finite backend outcomes, including cached,
unavailable, malformed and failed replies. No model, compiler, filesystem or network effects.
"""
import json

import retrieval_loop

SNAPSHOT = "a" * 64
FORMALISM = {"schema": 1, "id": "formalism-v1", "source_commit": "b" * 40,
             "modules": ["Library.Module"], "anchors": ["Library.Module.theorem"],
             "semantic_notes": ["Use the stated quotient semantics."]}


def check(name, condition):
    assert condition, name
    print("ok: " + name, flush=True)


def request(kind="check_candidate", **changes):
    value = {"action": kind, "proof": None, "query": None, "name": None, "reason": None}
    if kind == "check_candidate":
        value["proof"] = "by\n  rfl"
    return json.dumps({**value, **changes})


class Backend:
    def __init__(self, replies=()):
        self.calls, self.replies = [], list(replies)

    def call(self, operation, payload):
        self.calls.append((operation, payload))
        response = self.replies.pop(0) if self.replies else {
            "status": "ok", "snapshot": SNAPSHOT, "receipt": "c" * 64,
            "cached": True, "declaration": "retrieved text is evidence"}
        if isinstance(response, OSError):
            raise response
        return response


def protocol():
    check("strict typed-name schema", retrieval_loop.SCHEMA["properties"]["name"]["items"]["type"] == "string")
    valid = [request(), request("search", query="ZMod, _ + _ = 0"),
             request("read_declaration", name=["FTQCLib", "CSS", "cssX_correct_of_weights_le"]),
             request("read_declaration", name=["Ω", "lemma₁'"]), request("blocked", reason="missing prerequisite")]
    check("all declared actions admitted", all(retrieval_loop.action(raw, requests_left=2)[1] is None for raw in valid))
    bad = [request("bash", command="echo stolen"), request("shell"), request("read_file", path="/etc/passwd"),
           request("custom"), request(command="lake build"), request(snapshot="b" * 64),
           request("read_declaration", name="Library.Module.theorem"),
           request("read_declaration", name=["../answers"]), request("read_declaration", name=["a\\b"]),
           request("read_declaration", name=["a;bash"]), request("read_declaration", name=["$(id)"]),
           request("read_declaration", name=["Library.Module"]), request("read_declaration", name=[]),
           request("read_declaration", name=["a"] * 33), request("read_declaration", name=["Ω" * 129]),
           request(proof="\ud800"), request(proof="by\x00"), request(proof=7), request(query="unused"),
           request(proof="Ω" * (retrieval_loop.PROOF_BYTES_MAX // 2 + 1)),
           request("search", query="Ω" * 257), request("blocked", reason="x" * 2049),
           request().replace('"action":', '"action":"search","action":'),
           '{"action":NaN}', "[]", "null", "{", "[" * 2000, "x" * (retrieval_loop.RESPONSE_BYTES_MAX + 1)]
    backend = Backend()
    session = retrieval_loop.Session(backend, 2, SNAPSHOT)
    check("path, shell, extra fields, malformed and oversized actions refuse",
          all(session.dispatch(raw)["status"] == "refused" for raw in bad))
    check("refusals acquire no effects or budget", not backend.calls and session.requests_used == 0)


def budgets():
    backend = Backend()
    session = retrieval_loop.Session(backend, 2, SNAPSHOT)
    first = session.dispatch(request("search", query="Nat.add_comm"))
    second = session.dispatch(request("read_declaration", name=["Nat", "add_comm"]))
    check("search and reads dispatch typed payloads", backend.calls == [
        ("search", "Nat.add_comm"), ("read_declaration", ["Nat", "add_comm"])])
    check("cached requests share manifest budget", first["requests_used"] == 1 and second["requests_left"] == 0)
    check("both retrieval actions exhausted", session.dispatch(request("search", query="x"))["status"] == "refused"
          and session.dispatch(request("read_declaration", name=["Nat"]))["status"] == "refused" and len(backend.calls) == 2)
    check("candidate and blocked do not consume retrieval budget", session.dispatch(request())["status"] == "candidate"
          and session.dispatch(request("blocked", reason="missing proof"))["status"] == "blocked" and session.requests_used == 2)
    unavailable = {"status": "unavailable", "snapshot": SNAPSHOT, "receipt": "d" * 64}
    failing = retrieval_loop.Session(Backend([unavailable, OSError("bounded backend failure")]), 2, SNAPSHOT)
    check("unavailable receipt remains distinct", failing.dispatch(request("search", query="x"))["response"] == unavailable)
    failed = failing.dispatch(request("read_declaration", name=["Nat"]))
    check("backend failures consume reservation", failed["status"] == "retrieval_failed" and failing.requests_left == 0)
    for response in ({"snapshot": SNAPSHOT}, {"snapshot": "b" * 64, "receipt": "d" * 64},
                     {"snapshot": SNAPSHOT, "receipt": "d" * 64, "text": "x" * 32769}):
        selected = retrieval_loop.Session(Backend([response]), 1, SNAPSHOT)
        check("unbound or oversized backend data cannot become evidence",
              selected.dispatch(request("search", query="x"))["status"] == "retrieval_failed" and selected.retrieved is None)


def packets():
    anchors = {"snapshot": SNAPSHOT, "receipt": "e" * 64, "anchors": [{"name": ["Library", "theorem"], "type": "True"}]}
    packet = retrieval_loop.packet({"obligation": "True"}, FORMALISM, SNAPSHOT, requests_left=2,
                                   retrieved=anchors, latest="Ω" * 4000)
    check("versioned formalism and prefetched anchors preserved", packet["formalism"] == FORMALISM
          and packet["snapshot"] == SNAPSHOT and packet["retrieved"] == anchors)
    check("latest diagnostic byte bound explicit", packet["latest"]["truncated"]
          and len(packet["latest"]["text"].encode()) <= retrieval_loop.DIAGNOSTIC_BYTES_MAX)
    check("packet carries no accumulated transcript", set(packet) == {
          "schema", "evidence", "formalism", "snapshot", "capabilities", "requests_left", "latest", "retrieved", "protocol"})
    closed = retrieval_loop.packet({}, FORMALISM, SNAPSHOT, requests_left=0)
    check("exhausted packet advertises only candidate and blocked", closed["capabilities"] == ["check_candidate", "blocked"])
    cases = [lambda: retrieval_loop.packet({}, {**FORMALISM, "schema": 0}, SNAPSHOT, requests_left=1),
             lambda: retrieval_loop.packet({}, FORMALISM, "not-a-hash", requests_left=1),
             lambda: retrieval_loop.packet({}, FORMALISM, SNAPSHOT, requests_left=65),
             lambda: retrieval_loop.packet({}, FORMALISM, SNAPSHOT, requests_left=1, retrieved={"x": float("nan")}),
             lambda: retrieval_loop.packet({"x": "z" * 20000}, FORMALISM, SNAPSHOT, requests_left=1),
             lambda: retrieval_loop.Session(Backend(), True, SNAPSHOT)]
    for index, case in enumerate(cases):
        try:
            case()
        except ValueError:
            check("owner invalid input refused " + str(index), True)
        else:
            check("owner invalid input refused " + str(index), False)


if __name__ == "__main__":
    protocol()
    budgets()
    packets()
