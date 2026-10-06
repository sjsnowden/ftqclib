"""Typed owner scripts compiled into existing plan steps and addressed-question routes.

Names and effect destinations are declared before execution. Models propose values;
they never select executables, mutate plans or accept proofs. A function is an
unscheduled native answer endpoint, not a second scheduler or a proof retirement.
"""
import copy
import json
import re

import chain_protocol
import study

RESULT_SCHEMA = {"type": "object", "additionalProperties": False, "properties": {
    "status": {"type": "string", "enum": ["evidence", "prerequisite", "adaptation", "needs_operator"]},
    "body": {"type": "string", "maxLength": 8192},
    "declarations": {"type": "array", "minItems": 0, "maxItems": 4,
                     "items": {"type": "string", "minLength": 1, "maxLength": 256}}},
    "required": ["status", "body", "declarations"]}


def validate(program, nodes):
    if not isinstance(program, dict) or set(program) != {"schema", "functions", "on_blocked", "message_limit", "max_model_calls"}:
        raise ValueError("proof program requires schema, functions, on_blocked, message_limit and max_model_calls")
    if type(program["schema"]) is not int or program["schema"] != 1 or type(program["message_limit"]) is not int or not 1 <= program["message_limit"] <= 4:
        raise ValueError("proof program schema or message limit differs")
    if type(program["max_model_calls"]) is not int or not 1 <= program["max_model_calls"] <= 128:
        raise ValueError("program model-call budget must be 1..128")
    functions, known, names = program["functions"], {node["id"] for node in nodes}, set()
    if not isinstance(functions, dict) or not 1 <= len(functions) <= 8:
        raise ValueError("declare one to eight model functions")
    for name, function in functions.items():
        if not re.fullmatch(r"[a-z][a-z0-9_]{0,63}", name):
            raise ValueError("function name is not a bounded identifier")
        if not isinstance(function, dict) or set(function) != {"step", "purpose", "model", "effort", "evidence"}:
            raise ValueError("function requires step, purpose, model, effort and evidence")
        if not isinstance(function["step"], str) or not re.fullmatch(r"T\d\d\.M(?:\.\d+)?", function["step"]) or function["step"] in known | names:
            raise ValueError("function endpoint must have a unique native model-step ID")
        names.add(function["step"])
        for field in ("purpose", "model", "effort"):
            if not isinstance(function[field], str) or not 0 < len(function[field].encode()) <= 4096:
                raise ValueError("function text is empty or over its bound")
        if any(function[field].startswith("-") or len(function[field]) > 200 for field in ("model", "effort")):
            raise ValueError("bounded model and effort identifiers required")
        if not isinstance(function["evidence"], list) or len(function["evidence"]) > 12:
            raise ValueError("function evidence list bound")
        if any(chain_protocol.name_refusal(value) for value in function["evidence"]):
            raise ValueError("function evidence must name exact Lean declarations")
    if not isinstance(program["on_blocked"], dict) or set(program["on_blocked"]) - known or any(
            not isinstance(value, str) or value not in functions for value in program["on_blocked"].values()):
        raise ValueError("blocked routes must name declared proof nodes and functions")
    return program


def compile_steps(program):
    return [{"id": fn["step"], "target": fn["step"].split(".")[0], "kind": "proof",
             "scheduled": False, "title": name + ": " + fn["purpose"], "artifact": "typed advice",
             "gate": "Answer schema; sender retains proof checking", "depends_on": [], "writes": [],
             "agent": {"model": fn["model"], "effort": fn["effort"]}, "model_function": name}
            for name, fn in program["functions"].items()]


def config(program):
    return {"control_enabled": True, "attempt_mailboxes": True,
            "message_limit": program["message_limit"], "message_routes": {
                node: [program["functions"][name]["step"]] for node, name in program["on_blocked"].items()}}


def result(raw):
    if not isinstance(raw, str) or len(raw.encode()) > 16384:
        raise ValueError("function result byte bound")
    value = json.loads(raw, object_pairs_hook=chain_protocol.limits.unique,
                       parse_constant=chain_protocol.limits.invalid_constant)
    if not isinstance(value, dict) or set(value) != set(RESULT_SCHEMA["required"]):
        raise ValueError("model function result shape differs")
    if value["status"] not in RESULT_SCHEMA["properties"]["status"]["enum"]:
        raise ValueError("unknown function result tag")
    if not chain_protocol.limits.valid_text(value["body"], 8192):
        raise ValueError("function answer body bound")
    names = value["declarations"]
    if not isinstance(names, list) or len(names) > 4 or any(chain_protocol.name_refusal(name) for name in names):
        raise ValueError("function declaration names differ")
    return value


def question(program, node, reason, note):
    name = program["on_blocked"].get(node)
    if name is None:
        return None
    return {"schema": 1, "to": program["functions"][name]["step"],
            "body": json.dumps({"function": name, "request": reason}, ensure_ascii=False),
            "continuation": note[:4000]}


def plan_nodes(plan, manifest):
    """Only predeclared proof definitions can run; versioned plans can select evidence and future order."""
    original = {node["id"]: node for node in manifest["nodes"]}
    nodes = []
    for step in plan["steps"]:
        if "model_function" in step:
            continue
        if step["id"] not in original:
            raise ValueError("new theorem definitions require a new study manifest and controls")
        node = copy.deepcopy(original[step["id"]])
        if step["writes"] != [node["path"], ".ontologic/certificates/" + node["id"] + ".json"]:
            raise ValueError("plan changes protected proof output destinations")
        if step["depends_on"] != node["deps"]:
            raise ValueError("new mathematical dependencies require a new study manifest")
        evidence = step.get("proof_evidence", node["evidence"])
        if (not isinstance(evidence, list) or len(evidence) > 16 or any(not isinstance(parts, list)
                or any(not isinstance(part, str) for part in parts)
                or chain_protocol.name_refusal(".".join(parts)) for parts in evidence)):
            raise ValueError("plan evidence must be bounded declaration names")
        node["evidence"] = evidence
        nodes.append(node)
    return nodes
