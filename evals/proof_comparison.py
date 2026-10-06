"""Derive token comparisons from recorded outcomes; failed work is never a free saving."""
import argparse
import json
from pathlib import Path
import statistics


def group(rows):
    known = [row for row in rows if type(row.get("tokens")) is int]
    accepted = [row for row in rows if row["assessment"] == "accepted"]
    categories = ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens", "output_tokens")
    totals = {key: sum(row["usage"][key] for row in known) for key in categories}
    return {"trials": len(rows), "accepted": len(accepted), "unknown_usage": len(rows) - len(known),
            "tokens": [row.get("tokens") for row in rows],
            "mean_tokens": statistics.mean(row["tokens"] for row in known) if known else None,
            "median_tokens": statistics.median(row["tokens"] for row in known) if known else None,
            "mean_usage": {key: value / len(known) if known else None for key, value in totals.items()},
            "total_tokens_per_accepted": sum(row["tokens"] for row in known) / len(accepted)
            if accepted and len(known) == len(rows) else None,
            "model_calls": [row.get("model_calls") for row in rows]}


def compare(historical, current):
    baseline = group(historical["slots"])
    arms = {condition: group([row for row in current["trials"] if row["condition"] == condition])
            for condition in ("A", "B")}
    for arm in arms.values():
        arm["mean_token_reduction_percent"] = (100 * (1 - arm["mean_tokens"] / baseline["mean_tokens"])
                                                if arm["mean_tokens"] is not None and baseline["mean_tokens"] else None)
    return {"historical_study": historical["study"], "current_study": current["study"],
            "historical_full_agent": baseline, "compact_local": arms["A"], "compact_loogle": arms["B"],
            "interpretation": ["Same F01 source obligation, pinned compiler and final acceptance checks.",
                               "Historical full-agent baseline has one observation; compact arms have repeated fresh trials.",
                               "This measures bundled workflow changes, not an isolated causal effect of prompt length.",
                               "Cached tokens are included once; cost is unknown, not zero.",
                               "A versus B compares local evidence with local evidence plus shared Loogle prefetch and bounded follow-up search.",
                               "No population-wide quality or savings claim follows from this development fixture."]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("historical", type=Path)
    parser.add_argument("current", type=Path)
    args = parser.parse_args()
    print(json.dumps(compare(json.loads(args.historical.read_bytes()), json.loads(args.current.read_bytes())), indent=2))


if __name__ == "__main__":
    main()
