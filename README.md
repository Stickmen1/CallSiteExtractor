# Call Role Extraction Pipeline

Pipeline for extracting Java method call sites, classifying
each call into a semantic role and enriching a ClassViz JSON file so
the roles can be visualized on class-to-class call edges.

The main labels are:

- `Query/Retrieve`
- `Command/Mutate`
- `Control/Orchestrate`
- `Compute/Transform`
- `Validate/Guard`
- `Notify/Publish`
- `Creational`
- `Unknown/Mixed`

## What The Pipeline Does

For a Java project `X`, the pipeline works in three stages:

1. `CallExtractorRevised.java` parses the Java source code with Spoon and writes:
   - `calls.csv`: 85 static feature columns used by the classifier
   - `calls_context.csv`: caller/callee/line context for traceability
2. `classify_calls_with_jrip.py` applies the learned JRip rules and writes:
   - `classified_calls.json`: one predicted semantic label per call site
3. `enrich_classviz_with_call_roles.py` combines `classified_calls.json` with a
   normal ClassViz JSON file and writes an enriched ClassViz JSON where call edges
   have role metadata, colors, call-site details and proof traces.

## Requirements

- Java and Maven
- Python 3
- A Java source tree to analyze
- a ClassViz JSON file if you want the visualization enrichment step

## First Run On A Java Project

From this folder:

```bash
cd /path/to/CallSiteExtractor/call-extractor
```

Run the extractor and classifier:

```bash
python3 rule-learning/run_call_role_pipeline.py \
  --source-path /path/to/project-X/src/main/java \
  --project-root com.example.projectx \
  --project-name project-X
```

Use the package prefix of the analyzed project for `--project-root`. For example:

```bash
--project-root com.fsck.k9
--project-root nl.tudelft.jpacman
--project-root org.springframework.samples.petclinic
```

If you omit `--project-root`, the wrapper tries to infer it from Java package
declarations.

After this step the important outputs are:

```text
calls.csv
calls_context.csv
classified_calls.json
```

## Reuse Existing Extracted CSV Files

If `calls.csv` and `calls_context.csv` already exist and you only want to
regenerate the classification JSON:

```bash
python3 rule-learning/run_call_role_pipeline.py \
  --source-path /path/to/project-X/src/main/java \
  --project-root com.example.projectx \
  --project-name project-X \
  --skip-extraction
```

## Enrich A ClassViz JSON

If ClassViz has already produced a normal project JSON, combine it with the
classified calls:

```bash
python3 rule-learning/enrich_classviz_with_call_roles.py \
  --classviz-json /path/to/classviz-project.json \
  --classified-calls-json classified_calls.json \
  --output-json /path/to/project-X-call-roles.json \
  --max-call-site-details 0
```

The enriched JSON is still a ClassViz-compatible JSON file. Load it in ClassViz
the same way as a normal project JSON. The difference is that call edges now
include semantic role information such as:

- dominant call role
- role distribution
- JRip rule distribution
- individual call-site details
- proof trace for the rule that classified each call
- detailed class visualization and its connected edges to other classes
