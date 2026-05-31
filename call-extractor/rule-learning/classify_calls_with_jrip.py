"""
Classify extracted call sites with the improved JRip rule set.
The script reads the 85-feature calls.csv produced by CallExtractorRevised and
the optional calls_context.csv file, applies the learned JRip rules in order
and writes a JSON file that can be used to enrich ClassViz edges.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Callable


LABELS = [
    "Query/Retrieve",
    "Command/Mutate",
    "Control/Orchestrate",
    "Compute/Transform",
    "Validate/Guard",
    "Notify/Publish",
    "Creational",
    "Unknown/Mixed",
]

EVIDENCE_COLUMNS = [
    "MethodName",
    "NamePattern",
    "ReturnType",
    "IsVoidCall",
    "ResultUsageKind",
    "CalleeNameAction",
    "ComputeTransformNameHint",
    "CalleeBodySummary",
    "CalleeAnnotations",
    "ReceiverCategory",
    "ReceiverOrigin",
    "CallerLayer",
    "CalleeLayer",
    "LayerRelation",
    "ArgCount",
    "CallerMethodFanOut",
    "CallerClassFanOut",
    "CalleeMethodFanIn",
    "CalleeLooksQueryMethod",
    "CalleeLooksCommandMethod",
    "CalleeLooksValidatorMethod",
    "IsFactoryLikeCall",
    "InvocationFeedsAnotherCall",
    "BooleanLikeCall",
    "ReturnsExternalType",
    "ReceiverFieldInjectedDependency",
    "IsLoggingCall",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--calls-csv",
        type=Path,
        default=Path("calls.csv"),
        help="85-feature calls.csv produced by the extractor",
    )
    parser.add_argument(
        "--context-csv",
        type=Path,
        default=Path("calls_context.csv"),
        help="optional context CSV with Caller/Callee/Line columns",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=Path("classified_calls.json"),
        help="classified call-site JSON output",
    )
    parser.add_argument(
        "--project-name",
        default="unknown",
        help="project name to store in the JSON metadata",
    )
    return parser.parse_args()


def as_bool(row: dict[str, str], column: str) -> bool:
    return row.get(column, "").strip().lower() == "true"


def as_int(row: dict[str, str], column: str) -> int:
    value = row.get(column, "").strip()
    if not value:
        return 0
    try:
        return int(float(value))
    except ValueError:
        return 0


def split_member(member: str) -> tuple[str, str]:
    if not member or member == "UNKNOWN":
        return "UNKNOWN", "UNKNOWN"
    if "#" not in member:
        return "UNKNOWN", member
    class_name, method_name = member.split("#", 1)
    return class_name, method_name


def simple_name(qualified_name: str) -> str:
    if not qualified_name or qualified_name == "UNKNOWN":
        return "UNKNOWN"
    return qualified_name.rsplit(".", 1)[-1]


def feature_values(row: dict[str, str], columns: list[str]) -> dict[str, str]:
    return {column: row.get(column, "") for column in columns if column in row}


def rule(
    rule_id: str,
    label: str,
    condition: Callable[[dict[str, str]], bool],
    text: str,
    support: float,
    errors: float,
    evidence_columns: list[str],
) -> dict[str, object]:
    return {
        "ruleId": rule_id,
        "label": label,
        "condition": condition,
        "text": text,
        "support": support,
        "errors": errors,
        "evidenceColumns": evidence_columns,
    }


JRIP_RULES = [
    rule("JRIP-01", "Unknown/Mixed",
         lambda r: r.get("CalleeNameAction") == "LOGGER",
         "CalleeNameAction = LOGGER", 7.0, 0.0, ["CalleeNameAction"]),
    rule("JRIP-02", "Notify/Publish",
         lambda r: r.get("CalleeNameAction") == "NOTIFICATION",
         "CalleeNameAction = NOTIFICATION", 23.0, 0.0, ["CalleeNameAction"]),
    rule("JRIP-03", "Query/Retrieve",
         lambda r: r.get("NamePattern") == "query",
         "NamePattern = query", 161.0, 23.0, ["NamePattern"]),
    rule("JRIP-04", "Query/Retrieve",
         lambda r: r.get("MethodName") == "size",
         "MethodName = size", 4.0, 0.0, ["MethodName"]),
    rule("JRIP-05", "Query/Retrieve",
         lambda r: r.get("MethodName") == "empty",
         "MethodName = empty", 2.0, 0.0, ["MethodName"]),
    rule("JRIP-06", "Command/Mutate",
         lambda r: r.get("ResultUsageKind") == "IGNORED"
         and not as_bool(r, "CalleeLooksQueryMethod")
         and not as_bool(r, "IsFactoryLikeCall"),
         "ResultUsageKind = IGNORED AND CalleeLooksQueryMethod = false AND IsFactoryLikeCall = false",
         117.0, 6.0, ["ResultUsageKind", "CalleeLooksQueryMethod", "IsFactoryLikeCall"]),
    rule("JRIP-07", "Command/Mutate",
         lambda r: r.get("CalleeNameAction") == "MUTATOR" and r.get("CallerLayer") == "other",
         "CalleeNameAction = MUTATOR AND CallerLayer = other",
         31.0, 6.0, ["CalleeNameAction", "CallerLayer"]),
    rule("JRIP-08", "Command/Mutate",
         lambda r: not as_bool(r, "CalleeLooksQueryMethod") and not as_bool(r, "IsFactoryLikeCall"),
         "CalleeLooksQueryMethod = false AND IsFactoryLikeCall = false",
         12.0, 0.0, ["CalleeLooksQueryMethod", "IsFactoryLikeCall"]),
    rule("JRIP-09", "Command/Mutate",
         lambda r: r.get("CalleeNameAction") == "MUTATOR" and not as_bool(r, "IsVoidCall"),
         "CalleeNameAction = MUTATOR AND IsVoidCall = false",
         4.0, 0.0, ["CalleeNameAction", "IsVoidCall"]),
    rule("JRIP-10", "Validate/Guard",
         lambda r: as_bool(r, "CalleeLooksValidatorMethod"),
         "CalleeLooksValidatorMethod = true", 78.0, 0.0, ["CalleeLooksValidatorMethod"]),
    rule("JRIP-11", "Validate/Guard",
         lambda r: as_bool(r, "BooleanLikeCall"),
         "BooleanLikeCall = true", 42.0, 2.0, ["BooleanLikeCall"]),
    rule("JRIP-12", "Validate/Guard",
         lambda r: r.get("LayerRelation") == "other->unknown" and as_int(r, "CalleeMethodFanIn") >= 17,
         "LayerRelation = other->unknown AND CalleeMethodFanIn >= 17",
         25.0, 0.0, ["LayerRelation", "CalleeMethodFanIn"]),
    rule("JRIP-13", "Validate/Guard",
         lambda r: r.get("ResultUsageKind") == "PASSED_AS_ARGUMENT" and r.get("MethodName") == "nullable",
         "ResultUsageKind = PASSED_AS_ARGUMENT AND MethodName = nullable",
         2.0, 0.0, ["ResultUsageKind", "MethodName"]),
    rule("JRIP-14", "Compute/Transform",
         lambda r: as_bool(r, "ReturnsExternalType")
         and not as_bool(r, "IsFactoryLikeCall")
         and as_int(r, "CalleeMethodFanIn") >= 5,
         "ReturnsExternalType = true AND IsFactoryLikeCall = false AND CalleeMethodFanIn >= 5",
         53.0, 1.0, ["ReturnsExternalType", "IsFactoryLikeCall", "CalleeMethodFanIn"]),
    rule("JRIP-15", "Compute/Transform",
         lambda r: r.get("CalleeNameAction") == "CONVERSION",
         "CalleeNameAction = CONVERSION", 26.0, 0.0, ["CalleeNameAction"]),
    rule("JRIP-16", "Compute/Transform",
         lambda r: as_int(r, "CallerMethodFanOut") >= 20
         and as_int(r, "CallerClassFanOut") <= 16
         and as_bool(r, "InvocationFeedsAnotherCall"),
         "CallerMethodFanOut >= 20 AND CallerClassFanOut <= 16 AND InvocationFeedsAnotherCall = true",
         29.0, 0.0, ["CallerMethodFanOut", "CallerClassFanOut", "InvocationFeedsAnotherCall"]),
    rule("JRIP-17", "Compute/Transform",
         lambda r: r.get("MethodName") == "append",
         "MethodName = append", 13.0, 0.0, ["MethodName"]),
    rule("JRIP-18", "Compute/Transform",
         lambda r: r.get("MethodName") == "toString",
         "MethodName = toString", 12.0, 0.0, ["MethodName"]),
    rule("JRIP-19", "Compute/Transform",
         lambda r: r.get("ReceiverCategory") == "stream",
         "ReceiverCategory = stream", 4.0, 0.0, ["ReceiverCategory"]),
    rule("JRIP-20", "Compute/Transform",
         lambda r: r.get("MethodName") == "build" and as_int(r, "CallerClassFanOut") <= 8,
         "MethodName = build AND CallerClassFanOut <= 8",
         10.0, 1.0, ["MethodName", "CallerClassFanOut"]),
    rule("JRIP-21", "Compute/Transform",
         lambda r: r.get("ReturnType") == "java.util.stream.Stream",
         "ReturnType = java.util.stream.Stream", 3.0, 1.0, ["ReturnType"]),
    rule("JRIP-22", "Compute/Transform",
         lambda r: r.get("MethodName") == "toList",
         "MethodName = toList", 2.0, 0.0, ["MethodName"]),
    rule("JRIP-23", "Creational",
         lambda r: r.get("CalleeNameAction") == "CREATION",
         "CalleeNameAction = CREATION", 160.0, 0.0, ["CalleeNameAction"]),
    rule("JRIP-24", "Control/Orchestrate",
         lambda r: True,
         "default rule", 180.0, 26.0, []),
]


FEATURE_TRACE_SPECS = {
    "NamePattern": {
        "helper": "deriveNamePattern(lowerMethodName)",
        "logic": (
            "The extractor lowercases MethodName and returns query when the method name "
            "starts with get, find, fetch, load, or read."
        ),
        "values": [
            "MethodName",
            "NamePattern",
            "NameStartsWithGet",
            "NameStartsWithFind",
            "CalleeNameAction",
            "MethodLooksAccessor",
            "CalleeLooksQueryMethod",
        ],
    },
    "MethodName": {
        "helper": "executableRef.getSimpleName()",
        "logic": "The extractor reads the called executable simple name from the Spoon invocation reference.",
        "values": [
            "MethodName",
            "NamePattern",
            "CalleeNameAction",
            "MethodLooksAccessor",
            "MethodLooksMutator",
            "CalleeLooksQueryMethod",
            "CalleeLooksCommandMethod",
        ],
    },
    "ResultUsageKind": {
        "helper": "deriveResultUsageKind(invocation)",
        "logic": (
            "The extractor first records explicit result usage such as assignment, return, argument passing, "
            "condition use, comparison, null check, or chaining. If none are present, it marks the result "
            "as IGNORED when the invocation is void or effectively a standalone statement."
        ),
        "values": [
            "ResultUsageKind",
            "IsVoidCall",
            "AssignedToVariable",
            "ReturnedDirectly",
            "PassedAsArgument",
            "InIfCondition",
            "InvocationResultUsedInComparison",
            "InvocationResultUsedInNullCheck",
            "InvocationFeedsAnotherCall",
        ],
    },
    "CalleeLooksQueryMethod": {
        "helper": "looksLikeQueryMethod(methodName, returnType, null, null)",
        "logic": (
            "The extractor returns true for query-like names such as get, find, load, fetch, or list; "
            "it can also treat a non-void non-command call as query-like. False means those query conditions "
            "did not hold for this call."
        ),
        "values": [
            "MethodName",
            "CalleeLooksQueryMethod",
            "CalleeLooksCommandMethod",
            "NamePattern",
            "CalleeNameAction",
            "IsVoidCall",
            "ReturnType",
        ],
    },
    "IsFactoryLikeCall": {
        "helper": "looksLikeFactoryMethod(methodName, returnType)",
        "logic": "The extractor returns true when the method name starts with create, build, of, or from.",
        "values": [
            "IsFactoryLikeCall",
            "MethodName",
            "MethodNameStartsWithCreate",
            "MethodNameStartsWithBuild",
            "MethodNameStartsWithOf",
            "MethodNameStartsWithFrom",
            "ReceiverLooksLikeFactory",
            "ReturnsNewProjectType",
        ],
    },
    "CalleeNameAction": {
        "helper": "deriveCalleeNameAction(methodName)",
        "logic": (
            "The extractor maps method-name prefixes to action buckets such as LOGGER, ACCESSOR, FINDER, "
            "VALIDATOR, MUTATOR, NOTIFICATION, CONVERSION, CALCULATION, and CREATION."
        ),
        "values": [
            "MethodName",
            "CalleeNameAction",
            "NamePattern",
            "NameStartsWithGet",
            "NameStartsWithFind",
            "NameStartsWithSave",
            "NameStartsWithDelete",
            "NameStartsWithUpdate",
            "NameStartsWithNotify",
            "NameStartsWithPublish",
            "NameStartsWithEmit",
            "NameStartsWithDispatch",
            "NameStartsWithFire",
            "NameStartsWithSend",
            "ComputeTransformNameHint",
        ],
    },
    "CallerLayer": {
        "helper": "deriveLayer(callerPackage, callerType)",
        "logic": "The extractor infers the caller architectural layer from package/type naming and annotations.",
        "values": ["CallerLayer", "LayerRelation", "CrossLayerCall", "CallsDependencyField"],
    },
    "IsVoidCall": {
        "helper": "isVoidCall(invocation)",
        "logic": "The extractor checks whether the invocation static return type is void or unresolved as void.",
        "values": ["IsVoidCall", "ReturnType", "ResultUsageKind"],
    },
    "CalleeLooksValidatorMethod": {
        "helper": "looksLikeValidatorMethod(methodName, returnType)",
        "logic": (
            "The extractor returns true for validate, check, verify, or assert prefixes, and for boolean "
            "is/has-style calls."
        ),
        "values": [
            "CalleeLooksValidatorMethod",
            "MethodName",
            "NameContainsValidate",
            "NameContainsCheck",
            "BooleanLikeCall",
            "ReturnsBoolean",
            "ReturnType",
            "InvocationResultUsedInComparison",
            "InvocationResultUsedInNullCheck",
        ],
    },
    "BooleanLikeCall": {
        "helper": "isBooleanLikeCall(lowerMethodName, invocation.getType())",
        "logic": (
            "The extractor returns true when the method name starts with is, has, exists, can, or should, "
            "or when the static return type is boolean/Boolean."
        ),
        "values": [
            "BooleanLikeCall",
            "MethodName",
            "ReturnsBoolean",
            "ReturnType",
            "InIfCondition",
            "InvocationResultUsedInComparison",
            "InvocationResultUsedInNullCheck",
        ],
    },
    "LayerRelation": {
        "helper": "callerLayer + '->' + calleeLayer",
        "logic": "The extractor builds LayerRelation by concatenating the inferred caller and callee layers.",
        "values": ["CallerLayer", "CalleeLayer", "LayerRelation", "CrossLayerCall"],
    },
    "CalleeMethodFanIn": {
        "helper": "graphStats.methodFanIn(calleeSignature)",
        "logic": "The extractor counts how many caller methods invoke the same callee signature in the static call graph.",
        "values": ["CalleeMethodFanIn", "MethodName", "CalleeLayer", "LayerRelation"],
    },
    "ReturnsExternalType": {
        "helper": "returnsExternalType(invocation)",
        "logic": "The extractor checks whether the invocation return type is not inside the configured project root namespace.",
        "values": ["ReturnsExternalType", "ReturnType", "ReturnsProjectType", "IsVoidCall"],
    },
    "CallerMethodFanOut": {
        "helper": "graphStats.methodFanOut(callerSignature)",
        "logic": "The extractor counts how many distinct callees are invoked by the caller method.",
        "values": ["CallerMethodFanOut", "CallerClassFanOut", "InvocationFeedsAnotherCall", "InsideDelegationChain"],
    },
    "CallerClassFanOut": {
        "helper": "graphStats.classFanOut(callerClassName)",
        "logic": "The extractor counts how many distinct target classes are invoked by the caller class.",
        "values": ["CallerClassFanOut", "CallerMethodFanOut", "InvocationFeedsAnotherCall"],
    },
    "InvocationFeedsAnotherCall": {
        "helper": "invocationFeedsAnotherCall(invocation)",
        "logic": "The extractor marks true when the invocation result is used as the target or argument of another invocation.",
        "values": [
            "InvocationFeedsAnotherCall",
            "ResultUsageKind",
            "PassedAsArgument",
            "HasNestedInvocationArg",
            "InsideDelegationChain",
            "HasChainedOrNestedDelegation",
        ],
    },
    "ReceiverCategory": {
        "helper": "deriveReceiverCategory(invocation)",
        "logic": "The extractor categorizes the invocation receiver, including stream receivers for fluent stream calls.",
        "values": ["ReceiverCategory", "ReceiverOrigin", "ResultUsageKind", "InvocationFeedsAnotherCall"],
    },
    "ReturnType": {
        "helper": "invocation.getType()",
        "logic": "The extractor records the static Spoon return type of the invocation expression.",
        "values": [
            "ReturnType",
            "IsVoidCall",
            "ReturnsBoolean",
            "ReturnsCollection",
            "ReturnsOptional",
            "ReturnsProjectType",
            "ReturnsExternalType",
        ],
    },
}


def parse_condition_part(part: str) -> tuple[str, str, str] | None:
    for operator in (">=", "<=", "="):
        token = f" {operator} "
        if token in part:
            left, right = part.split(token, 1)
            return left.strip(), operator, right.strip()
    return None


def condition_trace_for_part(row: dict[str, str], condition_part: str) -> dict[str, object]:
    parsed = parse_condition_part(condition_part)
    if parsed is None:
        return {
            "conditionPart": condition_part,
            "extractorFeature": "default",
            "extractorLogic": "No earlier JRip rule matched this call site, so JRip used the default rule.",
            "actualValues": feature_values(row, [
                "MethodName", "NamePattern", "ResultUsageKind", "CalleeNameAction",
                "IsVoidCall", "ReturnType", "CalleeLooksQueryMethod", "IsFactoryLikeCall"
            ]),
        }

    feature, operator, expected = parsed
    spec = FEATURE_TRACE_SPECS.get(feature, {
        "helper": feature,
        "logic": f"The extractor produced {feature}; JRip compared it with {expected}.",
        "values": [feature],
    })
    actual = row.get(feature, "")
    return {
        "conditionPart": condition_part,
        "extractorFeature": feature,
        "operator": operator,
        "expectedValue": expected,
        "actualValue": actual,
        "extractorHelper": spec["helper"],
        "extractorLogic": spec["logic"],
        "actualValues": feature_values(row, spec["values"]),
    }


def build_condition_trace(row: dict[str, str], rule_text: str) -> list[dict[str, object]]:
    if rule_text == "default rule":
        return [condition_trace_for_part(row, rule_text)]
    return [condition_trace_for_part(row, part.strip()) for part in rule_text.split(" AND ")]


def classify(row: dict[str, str]) -> dict[str, object]:
    for current_rule in JRIP_RULES:
        condition = current_rule["condition"]
        if condition(row):
            evidence_columns = current_rule["evidenceColumns"]
            return {
                "label": current_rule["label"],
                "ruleId": current_rule["ruleId"],
                "rule": current_rule["text"],
                "ruleSupport": current_rule["support"],
                "ruleErrors": current_rule["errors"],
                "evidence": {column: row.get(column, "") for column in evidence_columns},
                "conditionTrace": build_condition_trace(row, str(current_rule["text"])),
            }
    raise AssertionError("JRIP default rule should always match")


def read_csv_rows(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise SystemExit(f"{path} has no header")
        return list(reader.fieldnames), list(reader)


def role_counts_for_edges(calls: list[dict[str, object]]) -> list[dict[str, object]]:
    grouped: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    for call in calls:
        grouped[(str(call["callerClass"]), str(call["calleeClass"]))].append(call)

    edges = []
    for (source_class, target_class), grouped_calls in sorted(grouped.items()):
        counts = Counter(str(call["label"]) for call in grouped_calls)
        dominant_label, dominant_count = counts.most_common(1)[0]
        edges.append({
            "sourceClass": source_class,
            "sourceSimpleName": simple_name(source_class),
            "targetClass": target_class,
            "targetSimpleName": simple_name(target_class),
            "dominantCallRole": dominant_label,
            "dominantCallRoleCount": dominant_count,
            "callRoleCounts": dict(counts),
            "callSiteIds": [call["id"] for call in grouped_calls],
            "totalCallSites": len(grouped_calls),
        })
    return edges


def main() -> None:
    args = parse_args()
    _, call_rows = read_csv_rows(args.calls_csv)

    context_rows: list[dict[str, str]]
    if args.context_csv.exists():
        _, context_rows = read_csv_rows(args.context_csv)
        if len(context_rows) != len(call_rows):
            raise SystemExit(
                f"{args.calls_csv} has {len(call_rows)} rows but "
                f"{args.context_csv} has {len(context_rows)} rows"
            )
    else:
        context_rows = [{} for _ in call_rows]

    classified_calls = []
    for idx, (features, context) in enumerate(zip(call_rows, context_rows), start=1):
        result = classify(features)
        caller_class, caller_method = split_member(context.get("Caller", ""))
        callee_class, callee_method = split_member(context.get("Callee", ""))
        line_text = context.get("Line", "")
        try:
            line = int(line_text) if line_text else None
        except ValueError:
            line = None

        classified_calls.append({
            "id": idx,
            "project": args.project_name,
            "caller": context.get("Caller", ""),
            "callerSignature": context.get("CallerSignature", ""),
            "callerClass": caller_class,
            "callerMethod": caller_method,
            "callee": context.get("Callee", ""),
            "calleeSignature": context.get("CalleeSignature", ""),
            "calleeClass": callee_class,
            "calleeMethod": callee_method,
            "line": line,
            "methodName": features.get("MethodName", ""),
            "label": result["label"],
            "ruleId": result["ruleId"],
            "rule": result["rule"],
            "ruleSupport": result["ruleSupport"],
            "ruleErrors": result["ruleErrors"],
            "evidence": result["evidence"],
            "conditionTrace": result["conditionTrace"],
            "featureSummary": {column: features.get(column, "") for column in EVIDENCE_COLUMNS},
        })

    label_counts = Counter(str(call["label"]) for call in classified_calls)
    rule_counts = Counter(str(call["ruleId"]) for call in classified_calls)

    output = {
        "metadata": {
            "project": args.project_name,
            "sourceCallsCsv": str(args.calls_csv),
            "sourceContextCsv": str(args.context_csv) if args.context_csv.exists() else None,
            "model": "JRip/RIPPER",
            "modelSource": "training_dataset_1000_three_projects",
            "modelEvaluation": {
                "instances": 1000,
                "attributes": 86,
                "testMode": "10-fold cross-validation",
                "accuracy": 0.916,
                "kappa": 0.9003,
                "weightedF1": 0.916,
                "numberOfRules": 24,
            },
            "note": "Labels are rule-based static predictions, not runtime-proven behavior.",
        },
        "summary": {
            "totalCallSites": len(classified_calls),
            "labelCounts": dict(label_counts),
            "ruleCounts": dict(rule_counts),
        },
        "calls": classified_calls,
        "classToClassEdges": role_counts_for_edges(classified_calls),
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(output, indent=2), encoding="utf-8")
    print(f"wrote {len(classified_calls)} classified calls to {args.output_json}")
    print("label counts:")
    for label in LABELS:
        print(f"  {label}: {label_counts.get(label, 0)}")


if __name__ == "__main__":
    main()
