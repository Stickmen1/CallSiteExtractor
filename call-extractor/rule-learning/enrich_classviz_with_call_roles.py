"""
Enrich a ClassViz JSON graph with rule-based call-role classifications.

The script combines:

1. a ClassViz project JSON file and
2. classified_calls.json produced by classify_calls_with_jrip.py

and writes a ClassViz-compatible JSON file whose class-to-class call edges have
semantic call-role properties such as dominantCallRole and callRoleCounts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


CALL_ROLE_COLORS = {
    "Query/Retrieve": "#2f80ed",
    "Command/Mutate": "#d35400",
    "Control/Orchestrate": "#7b61ff",
    "Compute/Transform": "#219653",
    "Validate/Guard": "#f2c94c",
    "Notify/Publish": "#eb5757",
    "Creational": "#00a6a6",
    "Unknown/Mixed": "#828282",
}

CLASS_LEVEL_EDGE_LABELS_TO_REMOVE = {"calls", "constructs"}
RAW_OPERATION_EDGE_LABELS = {"invokes", "uses"}
DEFAULT_NODE_LABELS_TO_KEEP = {"Scope", "Type", "Category", "Problem", "BugType"}
STRUCTURAL_EDGE_LABELS_TO_KEEP = {
    "encloses",
    "contains",
    "specializes",
    "realizes",
    "implements",
    "succeeds",
    "dependsOn",
    "allowedDependency",
    "nests",
    "holds",
    "accepts",
    "returns",
    "returnType",
    "typed",
    "type",
    "aggregates",
    "composites",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--classviz-json", required=True, type=Path,
                        help="input ClassViz JSON graph")
    parser.add_argument("--classified-calls-json", required=True, type=Path,
                        help="classified_calls.json produced by the JRip classifier")
    parser.add_argument("--output-json", required=True, type=Path,
                        help="enriched ClassViz JSON output")
    parser.add_argument("--include-external-nodes", action="store_true",
                        help="create lightweight Type nodes for classified external callees")
    parser.add_argument("--max-call-site-details", type=int, default=0,
                        help="maximum detailed call-site records stored on each enriched edge; use 0 for all")
    parser.add_argument("--keep-raw-operation-edges", action="store_true",
                        help="keep original invokes/uses edges; default removes them for a class-level view")
    parser.add_argument("--keep-non-class-nodes", action="store_true",
                        help="keep extra raw nodes such as fields/parameters; default keeps a cleaner class-level view")
    return parser.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise SystemExit(f"{path} does not contain a JSON object")
    return data


def load_classviz_json(path: Path) -> dict[str, Any]:
    data = load_json(path)
    if not isinstance(data, dict) or "elements" not in data:
        raise SystemExit(f"{path} does not look like a ClassViz JSON object")
    if not isinstance(data["elements"], dict):
        raise SystemExit(f"{path} must use elements.nodes/elements.edges format")
    data["elements"].setdefault("nodes", [])
    data["elements"].setdefault("edges", [])
    return data


def labels_of(element: dict[str, Any]) -> list[str]:
    return element.get("data", {}).get("labels", []) or []


def data_of(element: dict[str, Any]) -> dict[str, Any]:
    return element.setdefault("data", {})


def properties_of(element: dict[str, Any]) -> dict[str, Any]:
    return data_of(element).setdefault("properties", {})


def edge_label(edge: dict[str, Any]) -> str:
    data = data_of(edge)
    return data.get("label") or ",".join(data.get("labels", []) or []) or "nolabel"


def is_operation_node(node: dict[str, Any]) -> bool:
    labels = set(labels_of(node))
    kind = properties_of(node).get("kind")
    return bool(labels.intersection({"Operation", "Script", "Constructor"})) or kind in {"method", "ctor", "constructor", "script"}


def is_type_node(node: dict[str, Any]) -> bool:
    return "Type" in labels_of(node)


def is_default_visible_node(node: dict[str, Any]) -> bool:
    return bool(set(labels_of(node)).intersection(DEFAULT_NODE_LABELS_TO_KEEP))


def simple_name(qualified_name: str) -> str:
    if not qualified_name or qualified_name == "UNKNOWN":
        return "UNKNOWN"
    return qualified_name.rsplit(".", 1)[-1]


def stable_edge_id(source: str, target: str) -> str:
    digest = hashlib.sha1(f"{source}->{target}".encode("utf-8")).hexdigest()[:16]
    return f"call-role-{digest}"


def compact_call_site(call: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": call.get("id"),
        "caller": call.get("caller"),
        "callerSignature": call.get("callerSignature"),
        "callee": call.get("callee"),
        "calleeSignature": call.get("calleeSignature"),
        "line": call.get("line"),
        "methodName": call.get("methodName"),
        "label": call.get("label"),
        "ruleId": call.get("ruleId"),
        "rule": call.get("rule"),
        "ruleSupport": call.get("ruleSupport"),
        "ruleErrors": call.get("ruleErrors"),
        "evidence": call.get("evidence", {}),
        "conditionTrace": call.get("conditionTrace", []),
    }


def group_calls_by_class_edge(classified: dict[str, Any]) -> dict[tuple[str, str], list[dict[str, Any]]]:
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for call in classified.get("calls", []):
        source = call.get("callerClass") or "UNKNOWN"
        target = call.get("calleeClass") or "UNKNOWN"
        if source == "UNKNOWN" or target == "UNKNOWN" or source == target:
            continue
        grouped[(source, target)].append(call)
    return grouped


def make_external_type_node(qualified_name: str) -> dict[str, Any]:
    return {
        "data": {
            "id": qualified_name,
            "label": simple_name(qualified_name),
            "labels": ["Type"],
            "properties": {
                "simpleName": simple_name(qualified_name),
                "qualifiedName": qualified_name,
                "kind": "external class",
                "metaSrc": "call-role enrichment",
            },
        }
    }


def make_call_role_edge(source: str,
                        target: str,
                        calls: list[dict[str, Any]],
                        max_details: int) -> dict[str, Any]:
    counts = Counter(call.get("label", "Unknown/Mixed") for call in calls)
    dominant_label, dominant_count = counts.most_common(1)[0]
    rules = Counter(call.get("ruleId", "UNKNOWN") for call in calls)
    detail_limit = len(calls) if max_details <= 0 else max_details
    detailed = [compact_call_site(call) for call in calls[:detail_limit]]

    return {
        "data": {
            "id": stable_edge_id(source, target),
            "source": source,
            "target": target,
            "label": "calls",
            "interaction": "calls",
            "group": "calls",
            "properties": {
                "metaSrc": "call-role enrichment",
                "dominantCallRole": dominant_label,
                "dominantCallRoleColor": CALL_ROLE_COLORS.get(dominant_label, CALL_ROLE_COLORS["Unknown/Mixed"]),
                "dominantCallRoleCount": dominant_count,
                "callRoleCounts": dict(counts),
                "ruleCounts": dict(rules),
                "totalClassifiedCallSites": len(calls),
                "callSiteIds": [call.get("id") for call in calls],
                "callSiteDetails": detailed,
                "callSiteDetailsTruncated": max(0, len(calls) - len(detailed)),
            },
        }
    }


def annotate_raw_invokes(graph: dict[str, Any], classified: dict[str, Any]) -> int:
    by_signature: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for call in classified.get("calls", []):
        caller = call.get("callerSignature")
        callee = call.get("calleeSignature")
        if caller and callee:
            by_signature[(caller, callee)].append(call)

    annotated = 0
    for edge in graph["elements"]["edges"]:
        if edge_label(edge) != "invokes":
            continue
        data = data_of(edge)
        calls = by_signature.get((data.get("source"), data.get("target")))
        if not calls:
            continue
        props = properties_of(edge)
        counts = Counter(call.get("label", "Unknown/Mixed") for call in calls)
        dominant_label, dominant_count = counts.most_common(1)[0]
        props.update({
            "dominantCallRole": dominant_label,
            "dominantCallRoleColor": CALL_ROLE_COLORS.get(dominant_label, CALL_ROLE_COLORS["Unknown/Mixed"]),
            "dominantCallRoleCount": dominant_count,
            "callRoleCounts": dict(counts),
            "totalClassifiedCallSites": len(calls),
            "callSiteIds": [call.get("id") for call in calls],
        })
        annotated += 1

    return annotated


def enrich_graph(args: argparse.Namespace) -> dict[str, Any]:
    graph = load_classviz_json(args.classviz_json)
    classified = load_json(args.classified_calls_json)

    raw_invokes_annotated = annotate_raw_invokes(graph, classified)

    nodes = graph["elements"]["nodes"]
    type_node_ids = {data_of(node).get("id") for node in nodes if is_type_node(node)}
    type_node_ids.discard(None)

    allowed_nodes = []
    removed_node_ids = set()
    for node in nodes:
        node_id = data_of(node).get("id")
        if is_operation_node(node) or (not args.keep_non_class_nodes and not is_default_visible_node(node)):
            removed_node_ids.add(node_id)
        else:
            allowed_nodes.append(node)

    grouped_calls = group_calls_by_class_edge(classified)
    required_external_nodes = set()
    enriched_edges = []
    skipped_edges = 0

    for (source, target), calls in sorted(grouped_calls.items()):
        source_exists = source in type_node_ids
        target_exists = target in type_node_ids
        if not source_exists:
            skipped_edges += 1
            continue
        if not target_exists:
            if args.include_external_nodes:
                required_external_nodes.add(target)
            else:
                skipped_edges += 1
                continue
        enriched_edges.append(make_call_role_edge(source, target, calls, args.max_call_site_details))

    existing_ids = {data_of(node).get("id") for node in allowed_nodes}
    for external in sorted(required_external_nodes):
        if external not in existing_ids:
            allowed_nodes.append(make_external_type_node(external))

    kept_edges = []
    for edge in graph["elements"]["edges"]:
        data = data_of(edge)
        label = edge_label(edge)
        source = data.get("source")
        target = data.get("target")
        if source in removed_node_ids or target in removed_node_ids:
            continue
        if label in CLASS_LEVEL_EDGE_LABELS_TO_REMOVE:
            continue
        if not args.keep_raw_operation_edges and label in RAW_OPERATION_EDGE_LABELS:
            continue
        if label in STRUCTURAL_EDGE_LABELS_TO_KEEP or label not in RAW_OPERATION_EDGE_LABELS:
            kept_edges.append(edge)

    graph["elements"]["nodes"] = allowed_nodes
    graph["elements"]["edges"] = kept_edges + enriched_edges
    graph.setdefault("properties", {})
    graph["properties"]["schemaVersion"] = "1.0.0"
    graph["properties"]["callRoleEnrichment"] = {
        "sourceClassVizJson": str(args.classviz_json),
        "sourceClassifiedCallsJson": str(args.classified_calls_json),
        "model": classified.get("metadata", {}).get("model", "JRip/RIPPER"),
        "modelSource": classified.get("metadata", {}).get("modelSource", "training_dataset_1000_three_projects"),
        "modelEvaluation": classified.get("metadata", {}).get("modelEvaluation", {}),
        "callRoleColors": CALL_ROLE_COLORS,
        "rawInvokesAnnotatedBeforeClassLevelExport": raw_invokes_annotated,
        "classLevelCallEdgesAdded": len(enriched_edges),
        "classLevelCallEdgesSkipped": skipped_edges,
        "externalTypeNodesAdded": len(required_external_nodes),
        "note": "Call roles are static JRip rule predictions aggregated onto class-to-class call edges.",
    }

    return graph


def main() -> None:
    args = parse_args()
    enriched = enrich_graph(args)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(enriched, indent=2), encoding="utf-8")

    summary = enriched["properties"]["callRoleEnrichment"]
    print(f"wrote enriched ClassViz JSON to {args.output_json}")
    print(f"class-level call edges added: {summary['classLevelCallEdgesAdded']}")
    print(f"class-level call edges skipped: {summary['classLevelCallEdgesSkipped']}")
    print(f"external type nodes added: {summary['externalTypeNodesAdded']}")


if __name__ == "__main__":
    main()
