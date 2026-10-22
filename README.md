# Q-GUARD

Kotlin simulator and experiment code for Q-GUARD, a fidelity-aware entanglement-routing protocol with distributed purification planning, and its weighted-split extension, Q-GUARD-WS.

**Paper:** [Fidelity-Guaranteed Entanglement Routing with Distributed Purification Planning](https://arxiv.org/abs/2605.00246), Anthony Gatti, Anoosha Fayyaz, Prashant Krishnamurthy, Kaushik P. Seshadreesan, and Amy Babay.

This code builds on [Q-CAST / QuantumRouting](https://github.com/sshi27/QuantumRouting) by Shouqian Shi and Chen Qian. It retains the topology model, routing infrastructure, and Q-CAST baseline, and adds fidelity tracking, purification, Q-GUARD variants, and fidelity-qualified evaluation.

## Build and run

Requirements: a JDK and Maven. The simulator has been compiled with **OpenJDK 17 and Maven 3.9.9**; Kotlin and JVM dependencies are specified in `pom.xml`.

```bash
git clone https://github.com/anthony-gatti/q-guard.git
cd q-guard
mvn compile
mvn exec:java -Dexec.mainClass=quantum.Main
```

Run commands from the repository root. The simulation runs without a GUI, creates `dist/`, and writes one text log per algorithm and configuration. **The default command runs the full configured experiment suite**, including the hardware-heterogeneity sweep; it is not a short demo.

The separate plotting repository is **only required to render figures**. You do not need another copy of the Q-CAST simulator.

## Plot figures

Use the original [`sshi27/plot`](https://github.com/sshi27/plot) repository, as described in the [Q-CAST README](https://github.com/sshi27/QuantumRouting#run-demo-with-gui). Keep it next to `q-guard`, with the directory name `plot`: `q-guard/` and `plot/` must share a parent directory. Q-GUARD writes plotting data to `../plot/last-plot-data.json`.

In a separate terminal, starting from `q-guard/`:

```bash
git clone https://github.com/sshi27/plot.git ../plot
cd ../plot
python3.11 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt "matplotlib==3.7.5" "numpy<2"
MPLBACKEND=Agg python file-watcher.py
```

The upstream plotter uses `Tick.label`, which was [removed in Matplotlib 3.8](https://matplotlib.org/3.8.0/api/prev_api_changes/api_changes_3.8.0.html#unused-methods-in-axis-tick-xaxis-and-yaxis). Use Python 3.10 or 3.11 with the compatibility constraints above rather than installing the latest Matplotlib. `MPLBACKEND=Agg` allows rendering on a server without a display. The bundled font is loaded relative to the plotter's working directory, so start the watcher from `plot/`. For the intended typography, install Linux Libertine as a system font (for example, `sudo apt install fonts-linuxlibertine` on Debian/Ubuntu); otherwise Matplotlib may use a fallback font.

With the watcher running, return to `q-guard/` in the simulation terminal and generate the figure data:

```bash
mvn exec:java -Dexec.mainClass=quantum.Plot
```

The watcher renders PDFs into `../plot/dist/` and saves plotting-data snapshots in `../plot/back/`. Start it **before** running `quantum.Plot`; it reacts to file changes. The current Q-GUARD figure configuration disables LaTeX rendering, so TeX installation is not required for these figures.

Plotting expects the logs selected by `configs.kt` and `Plot.kt`. Missing or incomplete logs can produce empty or invalid series. In particular, the throughput-CDF routine also requests a `p = 0.3` case that is outside the default `pList`; generate matching data or adjust the plotted cases before interpreting that figure.

## Algorithms

The default experiment compares these four implementations:

| Source file in `src/main/kotlin/quantum/algorithm/` | Log name | Role |
| --- | --- | --- |
| `OnlineAlgorithm.kt` | `Online` | Q-CAST baseline; also the superclass of Q-GUARD |
| `Q_CAST_PUR.kt` | `Q-CAST-PUR` | Q-CAST with purification baseline |
| `Q_GUARD.kt` | `QG` | Q-GUARD |
| `Q_GUARD_WS_NFP.kt` | `QG-WS-NFP` | Weighted-split variant labeled **Q-GUARD-WS** in the current plots |

`Q_GUARD_FP.kt` and `Q_GUARD_WS.kt` are additional research variants and are not enabled in the default suite. Despite its filename, `Q_GUARD_WS.kt` is not the implementation selected by the current Q-GUARD-WS plots. The older `FidelityGuaranteedOnlineAlgorithm.kt` and `FidelityGuaranteedRouting.kt` prototypes are retained separately from the active comparisons.

## Experiment configuration

- [`configs.kt`](src/main/kotlin/quantum/configs.kt) defines node counts, average degrees, link and swap success probabilities, local-information ranges, concurrent request counts, topology indices, and fidelity thresholds. `allAvailableSettings` varies one parameter at a time around `referenceSetting`.
- [`main.kt`](src/main/kotlin/quantum/main.kt) selects algorithms, sets the number of simulated slots (`repeat` and `sweepRepeat`, both 1,000 by default), and defines the separate `tauSigma` sweep.
- [`Plot.kt`](src/main/kotlin/quantum/Plot.kt) selects figures, algorithms, and log configurations to read.

The default reference setting is 100 nodes, average degree 6, mean link success probability 0.7, swap success probability 0.9, `k = 3`, and 10 simultaneous source-destination pairs. The standard sweep uses a fidelity threshold of 0.75, with additional threshold values evaluated at the reference setting. `topoRange` currently contains one topology index.

Logs contain per-slot path results and a topology footer. Completed logs are skipped on subsequent runs when the completion separator is present. When changing code or configurations, move existing `dist/` logs aside or use a fresh checkout so old outputs are not mistaken for new results.

Topology and request generation use explicit seeds, but concurrent solvers share a random-number generator. A fixed seed alone does not guarantee identical stochastic outcomes across parallel runs.

## Repository structure

| Path | Contents |
| --- | --- |
| `src/main/kotlin/quantum/algorithm/` | Routing algorithms and Q-GUARD variants |
| `src/main/kotlin/quantum/topo/` | Topology, nodes, links, and delivered-pair fidelity accounting |
| `src/main/kotlin/quantum/Fidelity.kt` | Werner-state fidelity and BBPSSW calculations |
| `src/main/kotlin/quantum/PurificationUtils.kt` | Purification execution and planning helpers |
| `src/main/kotlin/quantum/main.kt` | Simulation entry point, `quantum.Main` |
| `src/main/kotlin/quantum/configs.kt` | Experiment settings and log parsing |
| `src/main/kotlin/quantum/Plot.kt` | Figure-data entry point, `quantum.Plot` |
| `src/main/kotlin/quantum/Visualizer.kt` | Optional Swing debugging utility |
| `src/main/kotlin/utils/` | Shared utilities |

## Docker

The image builds **this checkout** and runs the simulation. Plotting remains a separate host-side step using the instructions above.

```bash
docker build -t q-guard .
mkdir -p dist
docker run --rm -v "$(pwd)/dist:/workspace/q-guard/dist" q-guard
```

The mounted directory preserves simulation logs after the container exits. This runs the same full experiment suite as the Maven command.
