"""Goal: bounded proof proposals cannot evade admission or repeat expensive checks.

Method: finite scripted effect outcomes drive the real owner loop; a memory record
holds observations. No model, compiler, subprocess, network or filesystem effect
runs. Counterexamples cover unmatched usage, limits, stale transcript accumulation,
repeated candidates, refusal, unavailable checking and immediate acceptance.
"""
import json

import chain_check
import chain_runner
import chain_protocol
import study

SNAPSHOT = "a" * 64
USAGE = {"input_tokens": 7, "cache_read_input_tokens": 5,
         "cache_creation_input_tokens": 2, "output_tokens": 3}
FORMALISM = {"schema": 1, "modules": ["Library.Base"], "anchors": [], "semantic_notes": []}
NODE = {"id": "N1", "purpose": "Establish a consumer obligation", "header": "import Library.Base",
        "statement": "theorem Library.answer : True", "name": "Library.answer",
        "expected_type": "True", "path": "Library/Answer.lean", "module": "Library.Answer",
        "evidence": []}


class Memory:
    def __init__(self, entries=()):
        self.recorded, self.objects = list(entries), {}

    def entries(self):
        return list(self.recorded)

    def put(self, data):
        identity = study.digest(data)
        self.objects[identity] = data
        return identity


class Backend:
    snapshot = SNAPSHOT

    def __init__(self):
        self.calls = []

    def call(self, operation, payload):
        self.calls.append((operation, payload))
        base = {"status": "ok", "snapshot": SNAPSHOT, "receipt": "b" * 64}
        if operation == "search":
            return {**base, "count": 1, "hits_truncated": False,
                    "hits": [{"name": "Library.fact", "type": {"text": "True", "truncated": False}}]}
        return {**base, "name": payload, "kind": "theorem", "body": None,
                "type": {"text": "True", "truncated": False}}


class Checker:
    def __init__(self, outcomes=None):
        self.calls, self.outcomes = [], outcomes or {}

    def check(self, node, proof, issue):
        self.calls.append(proof)
        status = self.outcomes.get(proof, "failed")
        return {"accepted": status == "passed", "status": status, "diagnostic": "declared diagnostic"}


class Scripted(chain_runner.Runner):
    def __init__(self, replies, *, checker=None, max_calls=6, node_tokens=1000):
        manifest = {"id": "memory-study", "nodes": [NODE], "source_commit": "c" * 40,
                    "formalism": FORMALISM, "policy": {"max_requests": 2, "max_calls": max_calls,
                                                        "node_token_limit": node_tokens}}
        super().__init__("/unused", manifest, Memory(), checker or Checker(), Backend())
        self.replies, self.packets, self.events = list(replies), [], []

    def event(self, kind, **fields):
        self.events.append({"kind": kind, **fields})

    def launch(self, job, number, packet):
        self.packets.append(packet)
        return self.replies.pop(0)


def proposal(kind="check_candidate", proof="by\n  exact False.elim ?_", **changes):
    action = {"action": kind, "proof": proof if kind == "check_candidate" else None,
              "query": "True" if kind == "search_name" else None, "names": None,
              "reason": "missing premise" if kind == "blocked" else None}
    return {"admitted": True, "finished": True, "usage": dict(USAGE),
            "text": json.dumps(action), "worker_tool_calls": 0, **changes}


def run(runner, node=NODE):
    issue = {"hash": "d" * 64, "step": node["id"], "operands": []}
    return runner.rounds({"issue": issue, "step": node}, node, [])


def observations(kind, *, issue="i1", number=1, invocation="v1", usage=USAGE, **changes):
    return {"kind": kind, "study": "memory-study", "issue": issue, "round": number,
            "invocation": invocation, "usage": usage, **changes}


def admission():
    manifest = {"id": "memory-study", "execution": {"observed_token_limit": 34}}
    start, end = observations("proposal_start"), observations("proposal_end")
    assert chain_runner.admission(Memory(), manifest) is None
    assert chain_runner.known_usage(Memory([start, end]), "memory-study") == USAGE
    assert chain_runner.admission(Memory([start]), manifest) is not None
    assert chain_runner.admission(Memory([start, {**end, "usage": None}]), manifest) is not None
    assert chain_runner.admission(Memory([start, {**end, "usage": {}}]), manifest) is not None
    malformed = [([start, {**end, "issue": "other"}]),
                 ([start, {**end, "round": 2}]), ([start, start, end, end])]
    for entries in malformed:
        assert chain_runner.admission(Memory(entries), manifest) is not None, "unmatched usage admitted"
    second = [observations("proposal_start", number=2, invocation="v2"),
              observations("proposal_end", number=2, invocation="v2")]
    assert chain_runner.admission(Memory([start, end] + second), manifest) is not None
    unrelated = observations("proposal_start", study="other-study")
    assert chain_runner.admission(Memory([start, end, unrelated]), manifest) is None


def candidates():
    good, bad = "by\n  exact True.intro", "by\n  exact False.elim ?_"
    checker = Checker({good: "passed"})
    runner = Scripted([proposal(proof=bad), proposal(proof=bad), proposal(proof=good), proposal()], checker=checker)
    records, assessment, reason, searches, checks = run(runner)
    assert assessment["accepted"] and reason is None and len(records) == 3
    assert checker.calls == [bad, good] and checks == 2 and searches == 0
    assert len(runner.replies) == 1, "accepted proof caused an extra invocation"
    assert len([row for row in runner.events if row["kind"] == "trial_check"]) == 4
    assert runner.packets[0]["latest"] is None
    assert runner.packets[1]["latest"]["proof"]["text"] == bad
    assert all("messages" not in packet and "history" not in packet for packet in runner.packets)
    assert runner.packets[2]["evidence"]["failed_candidates"][0]["candidate"] == 1
    assert "issue" not in runner.packets[0]["evidence"]


def stopping():
    for reply in [proposal("blocked"), proposal(usage=None), proposal(usage={}),
                  proposal(finished=False, reason="deadline")]:
        runner = Scripted([reply, proposal()])
        records, assessment, reason, _, checks = run(runner)
        assert len(records) == 1 and len(runner.replies) == 1 and checks == 0 and assessment is None and reason
    runner = Scripted([proposal(), proposal()], node_tokens=sum(USAGE.values()))
    assert len(run(runner)[0]) == 1 and len(runner.replies) == 1
    runner = Scripted([proposal(), proposal()], max_calls=1)
    assert len(run(runner)[0]) == 1 and len(runner.replies) == 1
    checker = Checker({"by\n  exact False.elim ?_": "unavailable"})
    runner = Scripted([proposal(), proposal()], checker=checker)
    outcome = run(runner)
    assert len(outcome[0]) == 1 and "unavailable" in outcome[2] and len(runner.replies) == 1


def packets():
    runner = Scripted([proposal("search_name"), proposal("blocked")])
    outcome = run(runner)
    assert outcome[3] == 1 and runner.backend.calls == [("search", '"True"')]
    assert runner.packets[1]["requests_left"] == 1
    assert "Library.fact" in json.dumps(runner.packets[1]["retrieved"])
    large = {**NODE, "purpose": "x" * 17000}
    runner = Scripted([proposal()])
    try:
        run(runner, large)
    except ValueError as error:
        assert "bound" in str(error)
    else:
        raise AssertionError("oversized prompt context reached a model admission")
    assert not runner.packets and not runner.checker.calls
    source = chain_check.assembled(NODE, "by\n  exact True.intro")
    assert source.startswith((NODE["header"] + "\n\n" + NODE["statement"] + " := by\n").encode())
    for proof in ["by\n  simp", "by\n  trivial\naxiom injected : False", "by\n  run_tac pure ()", "x" * 16385]:
        try:
            chain_check.assembled(NODE, proof)
        except ValueError:
            pass
        else:
            raise AssertionError("out-of-contract proof admitted")


def retrieval_limits():
    malformed = proposal(text=json.dumps({"action": "search_name", "proof": None, "names": None,
                                         "query": "find a lemma about True", "reason": None}))
    runner = Scripted([malformed, malformed, proposal()])
    result = run(runner)
    assert len(result[0]) == 2 and "no new evidence" in result[2]
    assert not runner.backend.calls and not runner.checker.calls and len(runner.replies) == 1
    assert "retrieval_refusal" in runner.packets[1]["latest"]
    runner = Scripted([proposal(), proposal(), proposal(), proposal()])
    assert len(run(runner)[0]) == 3 and len(runner.checker.calls) == 1 and len(runner.replies) == 1
    batch = proposal(text=json.dumps({"action": "read_declarations", "proof": None,
                                     "names": ["Library.one", "Library.two"], "query": None, "reason": None}))
    runner = Scripted([batch, proposal("blocked")])
    assert run(runner)[3] == 2 and len(runner.packets) == 2 and len(runner.backend.calls) == 2
    assert "Library.one" in json.dumps(runner.packets[1]) and "Library.two" in json.dumps(runner.packets[1])
    runner = Scripted([proposal("search_name"), batch, proposal("blocked")])
    runner.manifest["policy"]["max_retrieval_rounds"] = 1
    assert run(runner)[3] == 1 and len(runner.backend.calls) == 1
    assert runner.packets[1]["requests_left"] == 0
    runner = Scripted([proposal("search_name"), proposal()])
    runner.backend.call = lambda *_: {"status": "ok", "snapshot": "wrong"}
    stopped = run(runner)
    assert len(stopped[0]) == 1 and "owner retrieval unavailable" in stopped[2]
    assert len(runner.replies) == 1 and not runner.checker.calls
    runner = Scripted([malformed, proposal()], max_calls=2)
    assert run(runner)[2] == "per-node model-call limit reached"


def check():
    admission()
    candidates()
    stopping()
    packets()
    retrieval_limits()
    print("Chain admission, bounded packets, repeated-candidate cache and stopping controls passed")


if __name__ == "__main__":
    check()
