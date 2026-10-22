package quantum

import quantum.algorithm.*
import quantum.topo.Topo
import utils.*
import java.io.BufferedWriter
import java.io.File
import java.io.FileWriter
import java.util.*
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.math.pow

fun sim() {
  val topos = topoRange.flatMap { idx ->
      randGen.setSeed(19900111L + idx * 7919L)
      (nList * dList).map { (n, d) ->
          Triple(n, d, idx) to Topo.generate(n, 0.9, 5, 0.1, d, lengthSigma = 0.35)
      }
  }.toMap()

  val alphaStore = ReducibleLazyEvaluation<Pair<Topo, Double>, Double>({ (topo, p) ->
    dynSearch(1E-10, 1.0, p, { x ->
      topo.links.map { Math.E.pow(-x * it.l) }.sum() / topo.links.size
    }, false, 0.001)
  })
  val repeat = 1000
  val OUT_DIR = "dist"
  File(OUT_DIR).mkdirs()

  val fixedFth = 0.75
  val (dRef, nRef, pRef, qRef, kRef, nsdRef) = referenceSetting

  // === FULL TEST SUITE ===
  topoRange.forEach { topoIdx ->
    val executor = Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors())
    randGen.setSeed(19900111L + topoIdx * 13L)

    allAvailableSettings.forEach { (d, n, p, q, k, nsd) ->
      val topo = topos[Triple(n, d, topoIdx)]!!
      val alpha = alphaStore[topo to p]

      val testSet = (1..repeat).map {
        (0 until n).shuffled(randGen).take(2 * nsd).chunked(2).map { it.toPair() }
      }

      val fths =
        if (d == dRef && n == nRef && p == pRef && q == qRef && k == kRef && nsd == nsdRef)
          fthList
        else
          listOf(fixedFth)

      fths.forEach { FTH ->
        val algorithms = synchronized(topo) {
          topo.q = q
          topo.k = k
          topo.alpha = alpha

          mutableListOf<Algorithm>(
            OnlineAlgorithm(Topo(topo), allowRecoveryPaths = true).apply {
              setDefaultThreshold(FTH)
            },
            Q_CAST_PUR(Topo(topo), allowRecoveryPaths = true).apply {
              setDefaultThreshold(FTH)
            },
            Q_GUARD(Topo(topo), allowRecoveryPaths = true).apply {
              setDefaultThreshold(FTH)
            },
            // Q_GUARD_FP(Topo(topo), allowRecoveryPaths = true).apply {
            //   setDefaultThreshold(FTH)
            // },
            // Q_GUARD_WS(Topo(topo), allowRecoveryPaths = true).apply {
            //   setDefaultThreshold(FTH)
            // },
            Q_GUARD_WS_NFP(Topo(topo), allowRecoveryPaths = true).apply {
              setDefaultThreshold(FTH)
            }
          ).filter { solver ->
            val settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)
            val done = try {
              File("$OUT_DIR/$settings.txt")
                .readLines().drop(2).any { line -> line.startsWith("--") }
            } catch (e: Exception) { false }
            if (done) println("skip $settings")
            !done
          }
        }

        algorithms.forEach { solver ->
          solver.settings = id(n, topoIdx, q, k, p, d, nsd, solver.name, FTH)
          val fn = "$OUT_DIR/${solver.settings}.txt"

          executor.execute {
            println(solver.topo.getStatistics())
            solver.logWriter = BufferedWriter(FileWriter(fn))
            testSet.forEach {
              solver.work(it.map { Pair(solver.topo.nodes[it.first], solver.topo.nodes[it.second]) })
            }
            solver.logWriter.appendln("-----------")
            solver.logWriter.appendln(solver.topo.toString())
            solver.logWriter.appendln(solver.topo.getStatistics())
            solver.logWriter.close()
          }
        }
      }
    }

    executor.shutdown()
    executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS)
  }

  // === TAU SIGMA SWEEP ===
  val tauSigmaList = listOf(0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0)
  val (d0, n0, p0, q0, k0, nsd0) = referenceSetting
  val sweepFth = 0.75
  val sweepRepeat = 1000

  tauSigmaList.forEach { tauSigma ->
    println("=== tauSigma = $tauSigma ===")

    topoRange.forEach { topoIdx ->
      randGen.setSeed(19900111L + topoIdx * 7919L)
      val topo = Topo.generate(n0, 0.9, 5, 0.1, d0,
          lengthSigma = 0.35,
          tauMean = 9.5,
          tauSigma = tauSigma
      )

      val alpha = dynSearch(1E-10, 1.0, p0, { x ->
        topo.links.map { Math.E.pow(-x * it.l) }.sum() / topo.links.size
      }, false, 0.001)

      randGen.setSeed(19900111L + topoIdx * 13L)
      val testSet = (1..sweepRepeat).map {
        (0 until n0).shuffled(randGen).take(2 * nsd0).chunked(2).map { it.toPair() }
      }

      val tauTag = "%.1f".format(Locale.US, tauSigma)

      val algorithms = synchronized(topo) {
        topo.q = q0
        topo.k = k0
        topo.alpha = alpha

        listOf<Algorithm>(
          OnlineAlgorithm(Topo(topo), allowRecoveryPaths = true).apply {
            setDefaultThreshold(sweepFth)
          },
          Q_CAST_PUR(Topo(topo), allowRecoveryPaths = true).apply {
            setDefaultThreshold(sweepFth)
          },
          Q_GUARD(Topo(topo), allowRecoveryPaths = true).apply {
            setDefaultThreshold(sweepFth)
          },
          Q_GUARD_WS_NFP(Topo(topo), allowRecoveryPaths = true).apply {
            setDefaultThreshold(sweepFth)
          }
        )
      }

      val executor = Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors())

      algorithms.forEach { solver ->
        val fn = "$OUT_DIR/tausweep-${tauTag}-${topoIdx}-${solver.name}.txt"

        val done = try {
          File(fn).readLines().drop(2).any { line -> line.startsWith("--") }
        } catch (e: Exception) { false }

        if (done) {
          println("skip $fn")
          return@forEach
        }

        executor.execute {
          println("running $fn")
          solver.logWriter = BufferedWriter(FileWriter(fn))
          testSet.forEach {
            solver.work(it.map { Pair(solver.topo.nodes[it.first], solver.topo.nodes[it.second]) })
          }
          solver.logWriter.appendln("-----------")
          solver.logWriter.appendln(solver.topo.toString())
          solver.logWriter.appendln(solver.topo.getStatistics())
          solver.logWriter.close()
        }
      }

      executor.shutdown()
      executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS)
    }
  }
}

class Main {
  companion object {
    @JvmStatic
    fun main(args: Array<String>) {
      try {
        val l = args.map { it.toInt() }
        if (l.isNotEmpty()) nList = l
      } catch (e: Exception) {
      }
      sim()
    }
  }
}
