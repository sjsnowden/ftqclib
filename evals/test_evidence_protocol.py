"""Goal: typed needs cannot bypass the real owner's validation, cache or budget.

Method: scripted receipt-bearing backend observations and checker outcomes drive
Session and Runner. No live model, Lean build, network or proof-validity claim.
"""
import json

import chain_protocol
import chain_runner
import evidence_protocol as protocol
import test_chain_protocol as receipts
import test_chain_runner as runners


def response(outcome="need", need="declaration_names", **changes):
    value = {"outcome": outcome, "proof": None, "need": need if outcome == "need" else None,
             "names": ["Library.fact"] if outcome == "need" and need == "declaration_names" else None,
             "fragment": "fact" if outcome == "need" and need == "name_fragment" else None,
             "reason": "missing premise" if outcome == "blocked" else None}
    if outcome == "candidate":
        value["proof"] = "by\n  exact True.intro"
    return json.dumps({**value, **changes})


def owner(rows=(), *, budget=2, initial=()):
    backend = receipts.Backend(rows)
    session = protocol.Session(backend, budget, receipts.SNAPSHOT, initial)
    backend.session = session
    return session, backend


def effects():
    session, backend = owner([receipts.declaration("ECCLib.Coding.IsCosetLeaderMap")])
    explained = response(names=["ECCLib.Coding.IsCosetLeaderMap"], reason="Need the exact definition to prove the obligation.")
    assert session.dispatch(explained)["status"] == "retrieval_result"
    assert backend.calls == [("read_declaration", ["ECCLib", "Coding", "IsCosetLeaderMap"])]
    session, backend = owner([receipts.declaration("New.fact")], budget=1,
                             initial=[receipts.declaration(), receipts.declaration()])
    assert len(session.initial) == 1
    batch = response(names=["Library.fact", "New.fact"])
    assert session.dispatch(batch)["status"] == "retrieval_result"
    assert backend.calls == [("read_declaration", ["New", "fact"])]
    assert session.dispatch(batch)["status"] == "refused" and session.requests_used == 1
    assert session.dispatch(response(names=["Other"]))["status"] == "refused"
    assert session.dispatch(response("candidate"))["status"] == "candidate"
    assert session.dispatch(response("blocked"))["status"] == "blocked"
    session, backend = owner([receipts.search("Library.fact")])
    fragment = response(need="name_fragment", fragment="Ω.lemma₁'")
    assert session.dispatch(fragment)["status"] == "retrieval_result"
    assert backend.calls == [("search", json.dumps("Ω.lemma₁'", ensure_ascii=False))]
    assert session.dispatch(fragment)["status"] == "refused" and len(backend.calls) == 1
    session, backend = owner(budget=1)
    assert session.dispatch(response(names=["A", "B"]))["status"] == "refused"
    assert not backend.calls and session.requests_used == 0
    session, backend = owner([OSError("unavailable")])
    assert session.dispatch(response())["status"] == "retrieval_failed"
    assert session.dispatch(response())["status"] == "refused" and len(backend.calls) == 1
    session, backend = owner([{"status": "unavailable", "reason": "timed_out", "snapshot": receipts.SNAPSHOT,
                               "receipt": receipts.RECEIPT}])
    result = session.dispatch(response())
    assert result["status"] == "retrieval_failed" and "timed_out" in result["reason"]


def invalid():
    bad = [response(need=need) for need in [None, [], "search", "read_declaration", "shell"]]
    bad += [response(names=names) for names in [None, [], ["A", "A"], ["A"] * 5, [1],
                                               ["Ω" * 129], ["../file"], ["«name»"]]]
    bad += [response(need="name_fragment", fragment=fragment) for fragment in
            ["find a fact", '"fact"', "$(id)", "Ω" * 121, "a\x00b", "\ud800"]]
    bad += [response(proof="by rfl"), response(executable="bash"), response(outcome=[]),
            response(reason="x" * 2049), response(reason=""), response("candidate", reason="explanation"),
            response("candidate", proof="x" * 16385), response("blocked", reason=""),
            response().replace('"need":', '"need":"name_fragment","need":'),
            receipts.request(), "null", "[" * 2000, '{"outcome":NaN}', "x" * 131073]
    session, backend = owner()
    for raw in bad:
        assert session.dispatch(raw)["status"] == "refused"
    assert not backend.calls and session.requests_used == 0
    assert session.ineffective_requests == len(bad)


def runner():
    replies = [runners.proposal(text=response()), runners.proposal(text=response("candidate"))]
    worker = runners.Scripted(replies, checker=runners.Checker({"by\n  exact True.intro": "passed"}))
    worker.manifest["policy"]["protocol"] = 3
    result = runners.run(worker)
    assert result[1]["accepted"] and result[3:] == (1, 1)
    assert worker.backend.calls == [("read_declaration", ["Library", "fact"])]
    assert worker.checker.calls == ["by\n  exact True.intro"]
    assert all(packet["schema"] == 3 and "capabilities" not in packet for packet in worker.packets)
    assert "Library.fact" in json.dumps(worker.packets[1]["retrieved"])
    worker = runners.Scripted([runners.proposal(text=response()), runners.proposal(text=response("blocked"))])
    worker.manifest["policy"].update(protocol=3, max_retrieval_rounds=0)
    assert runners.run(worker)[3] == 0 and not worker.backend.calls
    assert not worker.packets[0]["evidence_needs_available"]
    assert chain_runner.selected_protocol({"policy": {}}) is chain_protocol
    for version in [1, 4, True, "3"]:
        try:
            chain_runner.selected_protocol({"policy": {"protocol": version}})
        except ValueError:
            pass
        else:
            raise AssertionError("unknown protocol admitted")


def check():
    effects()
    invalid()
    runner()
    for version, module in [(2, chain_protocol), (3, protocol)]:
        size = len(json.dumps(module.SCHEMA, ensure_ascii=False, separators=(",", ":")).encode())
        instruction = len(module.INSTRUCTIONS.encode())
        print(f"Protocol {version}: schema {size} + instructions {instruction} = {size + instruction} UTF-8 bytes")
    print("Scripted typed-evidence controls passed; no live model or Lean acceptance evidence")


if __name__ == "__main__":
    check()
