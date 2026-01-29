package quantum

import quantum.algorithm.*
import quantum.topo.Topo
import utils.*
import java.awt.event.WindowEvent
import java.io.BufferedWriter
import java.io.File
import java.io.FileWriter
import java.util.*
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import javax.swing.WindowConstants
import kotlin.math.pow

fun sim() {
  val topos = (nList * dList).map { (n, d) ->
    n to d to Topo.generate(n, 0.9, 5, 0.1, d, lengthSigma = 0.35)
  }.toMap()
  
  val alphaStore = ReducibleLazyEvaluation<Pair<Topo, Double>, Double>({ (topo, p) ->
    dynSearch(1E-10, 1.0, p, { x ->
      topo.links.map { Math.E.pow(-x * it.l) }.sum() / topo.links.size
    }, false, 0.001)
  })
  val repeat = 1000

  // Quick switches - remove when done
  val OUT_DIR = "dist"
  File(OUT_DIR).mkdirs()

  val RUN_FTH_CHART = true
  val RUN_P_CHART   = true
  val P_CHART_FTH   = 0.70

  
  topoRange.forEach { topoIdx ->
    val executor = Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors())
    
    // allAvailableSettings.forEach { (d, n, p, q, k, nsd) ->
    //   val topo = topos[n to d]!!
    //   val alpha = alphaStore[topo to p]
      
    //   val testSet = (1..repeat).map {
    //     (0 until n).shuffled(randGen).take(2 * nsd).chunked(2).map { it.toPair() }
    //   }

    //   fthList.forEach { FTH ->

    //     val algorithms = synchronized(topo) {
    //       topo.q = q
    //       topo.k = k
    //       topo.alpha = alpha

    //       val algorithms = mutableListOf<Algorithm>(
    //         OnlineAlgorithm(Topo(topo), allowRecoveryPaths = true).apply {
    //           setDefaultThreshold(FTH)
    //         },
    //         Q_CAST_PUR(Topo(topo), allowRecoveryPaths = true).apply {
    //           setDefaultThreshold(FTH)
    //         },
    //         Q_GUARD(Topo(topo), allowRecoveryPaths = true).apply {
    //           setDefaultThreshold(FTH)
    //         },
    //         Q_GUARD_FP(Topo(topo), allowRecoveryPaths = true).apply {
    //           setDefaultThreshold(FTH)
    //         }
    //       )

    //       algorithms.filter { solver ->
    //         val settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)

    //         val done = try {
    //           File("dist/$settings.txt")
    //             .readLines()
    //             .drop(2)
    //             .any { line -> line.startsWith("--") }
    //         } catch (e: Exception) {
    //           false
    //         }

    //         if (done) println("skip $settings")
    //         !done
    //       }
    //     }

    //     algorithms.forEach { solver ->
    //       solver.settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)
    //       val fn = "dist/${solver.settings}.txt"

    //       executor.execute {
    //         val topo = solver.topo
    //         println(topo.getStatistics())

    //         solver.logWriter = BufferedWriter(FileWriter(fn))

    //         testSet.forEach {
    //           solver.work(it.map { Pair(topo.nodes[it.first], topo.nodes[it.second]) })
    //         }

    //         solver.logWriter.appendln("-----------")
    //         solver.logWriter.appendln(topo.toString())
    //         solver.logWriter.appendln(topo.getStatistics())
    //         solver.logWriter.close()
    //       }
    //     }
    //   }
    // }

    // --- BEGIN BRIEF TESTS ---
    val (d0, n0, p0, q0, k0, nsd0) = referenceSetting
    val settingsToRun = mutableSetOf(referenceSetting)

    if (RUN_FTH_CHART) settingsToRun.add(referenceSetting)
    if (RUN_P_CHART) {
      pList.sorted().forEach { p -> settingsToRun.add(Tuple(d0, n0, p, q0, k0, nsd0)) }
    }

    settingsToRun.forEach { (d, n, p, q, k, nsd) ->
      val topo = topos[n to d]!!
      val alpha = alphaStore[topo to p]

      val testSet = (1..repeat).map {
        (0 until n).shuffled(randGen).take(2 * nsd).chunked(2).map { it.toPair() }
      }

      // Decide which FTH values to run for *this* setting:
      val fthsToRun = mutableSetOf<Double>()
      if (RUN_P_CHART) fthsToRun.add(P_CHART_FTH)
      if (RUN_FTH_CHART && d == d0 && n == n0 && p == p0 && q == q0 && k == k0 && nsd == nsd0) {
        fthsToRun.addAll(fthList)
      }

      fthsToRun.forEach { FTH ->
        val algorithms = synchronized(topo) {
          topo.q = q
          topo.k = k
          topo.alpha = alpha

          val algorithms = mutableListOf<Algorithm>(
            OnlineAlgorithm(Topo(topo), allowRecoveryPaths = true).apply { setDefaultThreshold(FTH) },
            Q_CAST_PUR(Topo(topo), allowRecoveryPaths = true).apply { setDefaultThreshold(FTH) },
            Q_GUARD(Topo(topo), allowRecoveryPaths = true).apply { setDefaultThreshold(FTH) },
            Q_GUARD_FP(Topo(topo), allowRecoveryPaths = true).apply { setDefaultThreshold(FTH) },
            Q_GUARD_WS(Topo(topo), allowRecoveryPaths = true).apply { setDefaultThreshold(FTH) }
          )

          algorithms.filter { solver ->
            val settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)

            val done = try {
              File("$OUT_DIR/$settings.txt")
                .readLines()
                .drop(2)
                .any { line -> line.startsWith("--") }
            } catch (e: Exception) {
              false
            }

            if (done) println("skip $settings")
            !done
          }
        }

        algorithms.forEach { solver ->
          solver.settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)
          val fn = "$OUT_DIR/${solver.settings}.txt"

          executor.execute {
            val topo = solver.topo
            println(topo.getStatistics())

            solver.logWriter = BufferedWriter(FileWriter(fn))

            testSet.forEach {
              solver.work(it.map { Pair(topo.nodes[it.first], topo.nodes[it.second]) })
            }

            solver.logWriter.appendln("-----------")
            solver.logWriter.appendln(topo.toString())
            solver.logWriter.appendln(topo.getStatistics())
            solver.logWriter.close()
          }
        }
      }
    }
    // --- END BRIEF TESTS ---

    executor.shutdown()
    executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS)
  }
}

fun simpleTest() {
  val netTopology = Topo.generate(50, 0.9, 5, 0.1, 6)
  
  val p = listOf(0.8, 0.5)
  val alphas = p.map { expectedAvgP ->
    var alpha = 0.1
    var step = 0.1
    var lastAdd = true
    
    while (true) {
      val topo = Topo(netTopology.toString().lines().mapIndexed { i, line -> if (i == 1) alpha.toString() else line }.joinToString("\n"))
      val avgP = topo.links.map { Math.E.pow(-alpha * it.l) }.sum() / topo.links.size
      
      if (Math.abs(avgP - expectedAvgP) / expectedAvgP < 0.001) break
      else if (avgP > expectedAvgP) {
        if (!lastAdd) step /= 2
        alpha += step
        lastAdd = true
      } else {
        if (lastAdd) step /= 2
        alpha -= step
        lastAdd = false
      }
    }
    
    alpha
  }
  
  val repeat = 1000
  
  val testSet = (1..10).map { nsd ->
    val combinations = netTopology.nodes.combinations(2)
    (1..repeat).map {
      combinations.shuffled(randGen).take(nsd).map { it[0].id to it[1].id }
    }
  }
  
  val children = mutableListOf<String>()
  
  p.zip(alphas).forEach { (p, a) ->
    val topo = Topo(netTopology.toString().lines().mapIndexed { i, line -> if (i == 1) a.toString() else line }.joinToString("\n"))
    println(topo.getStatistics())
    
    val algorithms = listOf(
      OnlineAlgorithm(Topo(topo), allowRecoveryPaths = true) ,
      Q_CAST_PUR(Topo(topo), allowRecoveryPaths = true),
      // FidelityGuaranteedOnlineAlgorithm(Topo(topo), allowRecoveryPaths = true).apply {
      //     setDefaultThreshold(FTH)
      // },
      Q_GUARD(Topo(topo), allowRecoveryPaths = true),
      Q_GUARD_FP(Topo(topo), allowRecoveryPaths = true)
//      , OnlineAlgorithmWithRecoveryPaths(Topo(topo))
//      , BotCap(Topo(topo)),  CreationRate(Topo(topo)),
//      SumDist(Topo(topo)),
//      SingleLink(Topo(topo))
//      , GreedyGeographicRouting(Topo(topo))
    )
    
    algorithms.forEach {
      it.logWriter = BufferedWriter(FileWriter("""dist/test-${it.name}.txt"""))
    }
    
    val results: MutableList<MutableList<Pair<Double, Double>>> = MutableList(algorithms.size, { mutableListOf<Pair<Double, Double>>() })
    algorithms.parallelStream().forEach { solver ->
      val topo = solver.topo
      
      var window: Visualizer? = null
      
      if (visualize) {
        window = Visualizer(solver)
        window.title = "Routing Quantum Entanglement - ${solver.name}"
        window.setDefaultCloseOperation(WindowConstants.HIDE_ON_CLOSE)
      }
      
      solver.prepare()
      
      results[algorithms.indexOf(solver)].addAll(
        testSet.drop(1).map {
          val result = it.map {
            solver.work(it.map { Pair(topo.nodes[it.first], topo.nodes[it.second]) })
          }
          val avgEntanglements = result.sumBy { it.first }.toDouble() / result.size
          val avgEntangled = result.sumBy { it.second }.toDouble() / result.size
          
          avgEntanglements to avgEntangled
        }
      )
      
      if (visualize)
        window?.dispatchEvent(WindowEvent(window, WindowEvent.WINDOW_CLOSING))
    }
    
    algorithms.forEach {
      it.logWriter.appendln("-----------")
      it.logWriter.appendln(topo.toString())
      it.logWriter.appendln(topo.getStatistics())
    }
    
    children += listOf("""
    {
      'name': 'num-ebit-pairs-${topo.n}-${p}-${topo.q}',
      'solutionList': ${algorithms.map { """"${it.name}"""" }},
      'xTitle': '\\# src-dst pairs in one time slot',
      'yTitle': '\\# success pairs',
      'x': ${(1..results[0].size).toList()},
      'y': ${results.map { it.map { it.first } }},
    }""".trimIndent(), """
    {
      'name': 'num-succ-pairs-${topo.n}-${p}-${topo.q}',
      'solutionList': ${algorithms.map { """"${it.name}"""" }},
      'xTitle': '\\# src-dst pairs in one time slot',
      'yTitle': '\\# entanglements',
      'x': ${(1..results[0].size).toList()},
      'y': ${results.map { it.map { it.second } }},
    }""".trimIndent()
    )
    
    File("../plot/last-plot-data.json").writeText(
      """
{
  'type': "line",
  'figWidth': 600,
  'figHeight': 350,
  'usetex': True,

  'legendLoc': 'best',
  'legendColumn': 1,

  'markerSize': 8,
  'lineWidth': 1,

  'xLog': False,
  'yLog': False,
  'xGrid': True,
  'yGrid': True,

  'xFontSize': 16,
  'xTickRotate': False,
  'yFontSize': 16,
  'legendFontSize': 14,
  'output': True,

  'children': $children
}
""")
  }
}

var visualize = true

class Main {
  companion object {
    @JvmStatic
    fun main(args: Array<String>) {
      visualize = try {
        val solver = OnlineAlgorithm(Topo.generate(50, 0.9, 5, 0.1, 6))
        solver.logWriter = BufferedWriter(FileWriter("""dist/test-gui.txt"""))
        
        val window = Visualizer(solver)
        window.title = "Routing Quantum Entanglement - ${solver.name}"
        window.setDefaultCloseOperation(WindowConstants.HIDE_ON_CLOSE)
        
        window.dispatchEvent(WindowEvent(window, WindowEvent.WINDOW_CLOSING))
        true
      } catch (e: java.lang.Exception) {
        print("WARNING: GUI not available. Ignore this? \n(The final results are the same. Only difference: \n you CANNOT see the network visualizer) [Y/N]")
        val scanner = Scanner(System.`in`)
        if (scanner.next().first().toLowerCase() == 'y')
          false
        else throw Exception("No GUI available, and user refuses to continue. ")
      }
      
      // simpleTest()
      try {
        val l = args.map { it.toInt() }
        if (l.isNotEmpty()) nList = l
      } catch (e: Exception) {
      }
      sim()
    }
  }
}
