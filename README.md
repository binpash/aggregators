# Automated Synthesis of Scalable Aggregators

Synthesizing high-performance, formally verified aggregators for UNIX command parallelization systems.

## Main Directories

- **`/sysnthesis`:** Synthesis engine
- **`/lean4`:** Utilities components for synthesis and verification
- **`/benchmarks`:** Aggregator benchmarking infrastructure, scripts, and inputs

  - simple-infra
  - covid-mts
  - nlp
  - oneliners
  - unix50

- **`/py-2`:** Hand-written python aggregator for comparison

- [Development Journal](https://docs.google.com/document/d/12ebNS5_1kkoFkpU3S3NS9DIrPAuxr-mCZgHv_gskQag/edit#heading=h.d7q5gi7oemm1)

## Run Docker

```bash
./run-container
```

## Run Benchmarks

See: [benchmark directions](/benchmarks/readme.md)
