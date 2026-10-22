# Q-GUARD

## Overview

This repository contains the Kotlin simulator and experiments for Q-GUARD, a fidelity-aware entanglement-routing protocol with distributed purification planning, and its weighted-split extension, Q-GUARD-WS.

**Paper:** [Fidelity-Guaranteed Entanglement Routing with Distributed Purification Planning](https://arxiv.org/abs/2605.00246).

The simulator builds on [Q-CAST / QuantumRouting](https://github.com/sshi27/QuantumRouting) by Shouqian Shi and Chen Qian.

## Setup

Use **Java 17 and Maven 3.9.9** to build the simulator:

```bash
git clone https://github.com/anthony-gatti/q-guard.git
cd q-guard
mvn compile
```

To generate figures, also install the original [plotting repository](https://github.com/sshi27/plot) alongside `q-guard/`. From the Q-GUARD repository root:

```bash
git clone https://github.com/sshi27/plot.git ../plot
cd ../plot
python3.11 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt "matplotlib==3.7.5" "numpy<2"
cd ../q-guard
```

The plotting environment uses Python 3.11 and an older Matplotlib version for compatibility with the upstream plotter.

## Experiments

Configure the experiments in `src/main/kotlin/quantum/`:

- `configs.kt`: network parameters, request counts, topology indices, and fidelity thresholds.
- `main.kt`: algorithms, number of simulated slots, and hardware-heterogeneity sweep.
- `Plot.kt`: figures and log configurations to plot.

The default comparison includes Q-CAST, Q-CAST-PUR, Q-GUARD, and Q-GUARD-WS. Run the full configured suite from the repository root:

```bash
mvn compile
mvn exec:java -Dexec.mainClass=quantum.Main
```

Simulation logs are written to `dist/`. Completed logs are skipped on subsequent runs; move previous results aside before rerunning modified experiments.

To render figures, start the plotting watcher in a separate terminal:

```bash
cd ../plot
source .venv/bin/activate
MPLBACKEND=Agg python file-watcher.py
```

Then, from `q-guard/`, generate the figure data:

```bash
mvn exec:java -Dexec.mainClass=quantum.Plot
```

PDFs are saved to `../plot/dist/`. Keep the watcher running while generating figure data, and ensure the cases selected in `Plot.kt` match the simulation logs.
