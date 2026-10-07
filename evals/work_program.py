"""Derive the initial Work IR and its unchanged native proof plan.

WORK-IR.md gives this bridge its meaning. Lowering regenerates every redundant
representation and refuses disagreement. The artifact describes preparation;
native versioned plans retain authority over future execution after activation.
"""
import copy
import importlib
import re

import chain_protocol
import fixtures
import proof_program

REGISTRY = {
    "proof.checked/v1": {"kind": "act", "inputs": {}, "variadic": "checked:LeanProof",
                         "outputs": {"proof": "checked:LeanProof"},
                         "effects": ["model", "retrieve", "check", "checkpoint"],
                         "seals": ["checked"], "requires_closed": {}},
    "proof.answer/v1": {"kind": "act", "inputs": {}, "variadic": None,
                        "outputs": {"advice": "result:ProofAdvice"},
                        "effects": ["model", "retrieve"], "seals": [], "requires_closed": {}}}
GRANTS = ["check", "checkpoint", "model", "retrieve"]
ADAPTER = "ftqclib.proof/v1"
NODE_REQUIRED = {"id", "deps", "module", "path", "header", "name", "statement",
                 "expected_type", "purpose", "evidence"}
NODE_OPTIONAL = {"imports", "evidence_notes", "consumer", "checks"}
EXECUTION_REQUIRED = {"provider", "executable", "model", "effort", "deadline_seconds",
                      "model_catalog", "model_catalog_sha256", "observed_token_limit"}


def legacy_plan(spec, execution, program=None, *, function_order=None):
    """The native definitions remain byte-equivalent to pre-IR preparation."""
    agent = {"model": execution["model"], "effort": execution["effort"]}
    steps = [{"id": item["id"], "target": "T01", "kind": "proof", "scheduled": True,
              "title": item["purpose"], "artifact": item["path"],
              "gate": "Protected Lean type and axiom checks", "depends_on": item["deps"],
              "writes": [item["path"], ".ontologic/certificates/" + item["id"] + ".json"],
              "agent": copy.deepcopy(agent)} for item in spec["nodes"]]
    if program:
        ordered = copy.deepcopy(program)
        if function_order is not None:
            ordered["functions"] = {name: program["functions"][name] for name in function_order}
        steps += proof_program.compile_steps(ordered)
    return {"steps": steps, "reviewed_steps": []}


def from_proof(spec, execution, program=None):
    """Build a detached declaration; compile/lower is the validation boundary."""
    return build_initial(spec, execution, program, list(program["functions"]) if program is not None else [])


def build_initial(spec, execution, program, function_order):
    """Freeze the legacy endpoint array order explicitly, never in a map's order."""
    core = importlib.import_module("work_ir")
    nodes = [core.node(item["id"], "proof.checked/v1",
                       inputs={"predecessor_" + str(index): core.ref(dep, "proof")
                               for index, dep in enumerate(item["deps"])},
                       params={"node": copy.deepcopy(item)},
                       writes=[item["path"], ".ontologic/certificates/" + item["id"] + ".json"])
             for item in spec["nodes"]]
    if program is not None:
        nodes += [core.node(fn["step"], "proof.answer/v1", mode="endpoint",
                            params={"function": name, "definition": copy.deepcopy(fn)})
                  for name in function_order for fn in [program["functions"][name]]]
    metadata = {"adapter": ADAPTER, "spec": copy.deepcopy(spec),
                "execution": copy.deepcopy(execution), "program": copy.deepcopy(program),
                "config": proof_program.config(program) if program is not None else {},
                "function_order": list(function_order)}
    return core.build(spec["id"], nodes, exports={item["id"]: core.ref(item["id"], "proof")
                                                for item in spec["nodes"]}, metadata=metadata)


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def texts(values, reason):
    require(isinstance(values, list), reason)
    require(all(isinstance(value, str) and value.strip() for value in values), reason)


def validate_node(item, known, paths, names):
    require(isinstance(item, dict), "mathematical node must be an object")
    require(NODE_REQUIRED <= set(item) <= NODE_REQUIRED | NODE_OPTIONAL, "unknown or missing mathematical node fields")
    for field in NODE_REQUIRED - {"deps", "evidence"}:
        require(isinstance(item[field], str) and bool(item[field].strip()), "node text must be nonblank")
    require(re.fullmatch(r"T[0-9]{2}\.[0-9]+", item["id"]) is not None, "node ID is not native-step shaped")
    require(item["id"] not in known, "duplicate mathematical node ID")
    require(re.fullmatch(r"FTQCLib\.CSS\.Decoder\.[A-Za-z][A-Za-z0-9]*", item["module"]) is not None,
            "module outside contribution namespace")
    require(item["path"] == item["module"].replace(".", "/") + ".lean", "module path differs")
    require(item["path"] not in paths, "duplicate module path")
    texts(item["deps"], "dependencies must be node IDs")
    require(len(item["deps"]) == len(set(item["deps"])), "duplicate mathematical dependency")
    require(set(item["deps"]) <= known, "dependencies must precede the node")
    require(item["name"] not in names, "duplicate theorem name")
    require(chain_protocol.name_refusal(item["name"]) is None, "invalid theorem name")
    require(item["statement"].startswith("theorem " + item["name"] + " :"), "statement declaration differs")
    require(item["statement"].split(":", 1)[1].strip() == item["expected_type"].strip(), "frozen expected type differs")
    evidence = item["evidence"]
    require(isinstance(evidence, list) and len(evidence) <= 64, "evidence bound differs")
    for parts in evidence:
        texts(parts, "evidence must contain name components")
        require(chain_protocol.name_refusal(".".join(parts)) is None, "invalid evidence declaration")
    for field in NODE_OPTIONAL - {"consumer"}:
        if field in item:
            texts(item[field], "node annotation must contain text")
    if "consumer" in item:
        consumer = item["consumer"]
        require(isinstance(consumer, dict) and set(consumer) == {"intent", "expected_name"}, "unknown consumer fields")
        require(isinstance(consumer["intent"], str) and bool(consumer["intent"].strip()), "consumer intent missing")
        require(consumer["expected_name"] == item["name"], "consumer declaration differs")
    known.add(item["id"])
    paths.add(item["path"])
    names.add(item["name"])


def validate_spec(spec):
    required = {"schema", "id", "source_commit", "semantic_notes", "nodes"}
    optional = {"status", "module_prefix", "proof_policy"}
    require(isinstance(spec, dict) and required <= set(spec) <= required | optional, "unknown or missing specification fields")
    require(type(spec["schema"]) is int and spec["schema"] == 1, "specification schema differs")
    require(spec["source_commit"] == fixtures.REVISION, "specification baseline differs")
    require(isinstance(spec["id"], str) and bool(spec["id"].strip()), "specification ID missing")
    texts(spec["semantic_notes"], "semantic notes must contain text")
    require(isinstance(spec["nodes"], list) and 1 <= len(spec["nodes"]) <= 32, "mathematical node count bound")
    known, paths, names = set(), set(), set()
    for item in spec["nodes"]:
        validate_node(item, known, paths, names)
    if "module_prefix" in spec:
        require(spec["module_prefix"] == "FTQCLib.CSS.Decoder", "module prefix differs")
    if "proof_policy" in spec:
        policy = spec["proof_policy"]
        require(isinstance(policy, dict) and set(policy) == {"worker_output", "stable_simp", "allowed_axioms", "acceptance"},
                "unknown mathematical policy fields")
        texts(policy["allowed_axioms"], "axiom policy must contain names")
        require(policy["allowed_axioms"] == ["propext", "Classical.choice", "Quot.sound"], "checker axiom policy differs")


def validate_execution(execution):
    require(isinstance(execution, dict) and EXECUTION_REQUIRED <= set(execution) <= EXECUTION_REQUIRED | {"proof_policy"},
            "unknown or missing execution fields")
    require(execution["provider"] == "codex", "proof provider differs")
    for field in EXECUTION_REQUIRED - {"deadline_seconds", "observed_token_limit"}:
        require(isinstance(execution[field], str) and bool(execution[field].strip()), "execution text missing")
    for field in ("model", "effort"):
        require(not execution[field].startswith("-") and len(execution[field]) <= 200, "bounded model/effort required")
    require(re.fullmatch(r"[0-9a-f]{64}", execution["model_catalog_sha256"]) is not None, "model catalog identity differs")
    for field, limit in (("deadline_seconds", 3600), ("observed_token_limit", 10000000)):
        require(type(execution[field]) is int and 1 <= execution[field] <= limit, "execution budget outside bound")
    if "proof_policy" in execution:
        validate_policy(execution["proof_policy"])


def validate_policy(policy):
    bounds = {"protocol": (2, 3), "max_calls": (1, 32), "max_requests": (0, 8), "node_token_limit": (1, 1000000),
              "max_retrieval_rounds": (0, 8), "max_ineffective_rounds": (1, 8)}
    fixed = {"concurrency": 1, "input_bytes_max": 32768,
             "unknown_usage_stops_admission": True,
             "token_limit": "soft admission threshold; one in-flight call can exceed it", "automatic_escalations": 0}
    require(isinstance(policy, dict) and set(policy) == set(bounds) | set(fixed), "unknown proof policy fields")
    for key, (low, high) in bounds.items():
        require(type(policy[key]) is int and low <= policy[key] <= high, "proof policy budget outside bound")
    for key, value in fixed.items():
        require(type(policy[key]) is type(value) and policy[key] == value, "protected proof policy differs")


def lower(ir):
    """Return structured refusal or an exactly reproduced initial native plan."""
    core = importlib.import_module("work_ir")
    compiled = core.compile(ir, REGISTRY, GRANTS)
    if not compiled["ok"]:
        return {**compiled, "spec": None, "execution": None, "program": None, "config": None, "plan": None}
    try:
        metadata = compiled["artifact"]["program"]["metadata"]
        require(isinstance(metadata, dict) and set(metadata) == {"adapter", "spec", "execution", "program", "config", "function_order"},
                "unknown or missing proof adapter metadata")
        require(metadata["adapter"] == ADAPTER, "proof adapter version differs")
        spec, execution, program = metadata["spec"], metadata["execution"], metadata["program"]
        validate_spec(spec)
        validate_execution(execution)
        if program is not None:
            proof_program.validate(program, spec["nodes"])
        order = metadata["function_order"]
        texts(order, "function order must contain declared names")
        require(len(order) == len(set(order)) and set(order) == (set(program["functions"]) if program else set()),
                "function order differs from declared endpoints")
        expected = build_initial(spec, execution, program, order)
        from store import canonical
        require(canonical(ir) == canonical(expected), "IR nodes, parameters, references, exports or config disagree with proof metadata")
        plan = legacy_plan(spec, execution, program, function_order=order)
        import plan_check
        require(not plan_check.refusals(plan, ()), "native kernel refuses the lowered proof plan")
    except (ValueError, TypeError, KeyError, IndexError, AttributeError) as error:
        return {"ok": False, "errors": [{"code": "proof_adapter", "path": "$", "reason": str(error)}],
                "artifact": None, "identity": None, "spec": None, "execution": None,
                "program": None, "config": None, "plan": None}
    return {**compiled, "spec": copy.deepcopy(spec), "execution": copy.deepcopy(execution),
            "program": copy.deepcopy(program), "config": copy.deepcopy(metadata["config"]), "plan": plan}
