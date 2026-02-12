package quantum

import utils.ReducibleLazyEvaluation
import java.io.File

class Plot {
  val children = mutableListOf<String>()
  
  fun plot() {
    File("../plot/last-plot-data.json").writeText(
      """
{
  "type": "line",
  "figWidth": 600,
  "figHeight": 350,
  "usetex": false,

  "legendLoc": "best",
  "legendColumn": 1,

  "markerSize": 8,
  "lineWidth": 1,

  "xLog": false,
  "yLog": false,
  "xGrid": false,
  "yGrid": false,

  "xFontSize": 22,
  "xTickRotate": false,
  "yFontSize": 22,
  "legendFontSize": 14,
  "output": true,
  "show": false,

  "children": $children
}
"""
    )
  }
  
  val nameMapping = mapOf("SL" to "SLMP", "Online" to "Q-CAST", "Online-R" to "Q-CAST\\\\R", "CR" to "Q-PASS", "CR-R" to "Q-PASS\\\\R", "Greedy_H" to "Greedy", "QG" to "Q-GUARD", "QG-FP" to "Q-GUARD-FP", "Q-CAST-PUR" to "Q-CAST-PUR", "QG-WS" to "Q-GUARD-WS")
  // val names = listOf("Online", "SL", "Greedy_H", "CR")
  val names = listOf("Online", "QG", "Q-CAST-PUR", "QG-WS")
  
  fun throughputCdf() {
    val nameMapping = mapOf("SL" to "SLMP", "Online" to "Q-CAST", "Greedy_H" to "Greedy", "QG" to "Q-GUARD", "QG-FP" to "Q-GUARD-FP", "Q-CAST-PUR" to "Q-CAST-PUR", "QG-WS" to "Q-GUARD-WS")
    // val names = listOf("Online", "SL", "Greedy_H", "CR", "BotCap", "SumDist", "MultiMetric")
    val names = listOf("Online", "QG", "Q-CAST-PUR", "QG-WS")
    
    (1..3).forEach { mode ->
      var (d, n, p, q, k, nsd) = referenceSetting
      if (mode == 2) p = 0.3
      else if (mode == 3) n = 400
      val fth = 0.7
      
      var max = 0
      
      val result = names.map { name ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }.map { it.majorPaths.sumBy { it.succ } }.groupBy { it }.map { (k, v) ->
          k to v.size
        }.sortedBy { it.first }.forEach { (k, v) ->
          max = Math.max(max, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max).map { sum[it] / s.toDouble() }
      }
      
      children.add("""
        {
          "markerSize": 0,
          "name": "${"throughput-cdf-$d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Throughput (eps)",
          "xTicks&Labels": ${(0..max).chunked(5).map { it.first() }},
          
          "xLimit": [0, $max],
          "yLimit": [0, 1],
          "x": ${(0..max).toList()},
          "y": ${result.map { l -> if (l.size < max + 1) l + List(max + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent())
    }
  }
  
  fun throughputNsd() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    val resultsQ = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    val results2Q = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    val results3Q = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "Throughput (eps)",
          "x": $nsdList,
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "# succ main paths",
          "x": $nsdList,
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "# succ S-D pairs",
          "x": $nsdList,
          "y": ${results3}
        }""".trimIndent(),
      """
        {
          "name": "${"qualified-throughput-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "Throughput (eps)",
          "x": $nsdList,
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "# succ main paths",
          "x": $nsdList,
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "# succ S-D pairs",
          "x": $nsdList,
          "y": ${results3Q}
        }""".trimIndent()
    )
  }
  
  fun throughputD() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    val resultsQ = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2Q = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3Q = names.map { name ->
      dList.sorted().map { d ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3}
        }""".trimIndent(),"""
        {
          "name": "${"qualified-throughput-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average node degree",
          "x": ${dList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3Q}
        }""".trimIndent()
    )
  }
  
  fun throughputP() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          // parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
          val fn = "dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt"
          if (!File(fn).exists()) {
            println("MISSING: $fn")
            return@flatMap emptyList<Record>()
          }
          parseLog(fn)
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }

    val resultsQ = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2Q = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3Q = names.map { name ->
      pList.sorted().map { p ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3}
        }""".trimIndent(),"""
        {
          "name": "${"qualified-throughput-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-$d-$n-p-$q-$k-$nsd".replace(".", "")}",
          "xTitle": "Average channel success rate",
          "x": ${pList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3Q}
        }""".trimIndent()
    )
  }
  
  fun throughputN() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    val resultsQ = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2Q = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3Q = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "Throughput (eps)",
          "x": ${nList.sorted()},
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "# succ main paths",
          "x": ${nList.sorted()},
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "# succ S-D pairs",
          "x": ${nList.sorted()},
          "y": ${results3}
        }""".trimIndent(),"""
        {
          "name": "${"qualified-throughput-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "Throughput (eps)",
          "x": ${nList.sorted()},
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "# succ main paths",
          "x": ${nList.sorted()},
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "# succ S-D pairs",
          "x": ${nList.sorted()},
          "y": ${results3Q}
        }""".trimIndent()
    )
  }
  
  fun throughputQ() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    val resultsQ = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2Q = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3Q = names.map { name ->
      qList.sorted().map { q ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3}
        }""".trimIndent(),"""
        {
          "name": "${"qualified-throughput-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-$d-$n-$p-q-$k-$nsd".replace(".", "")}",
          "xTitle": "Swapping success rate",
          "x": ${qList.sorted()},
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3Q}
        }""".trimIndent()
    )
  }
  
  fun throughputK() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val results = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    val results3 = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.succ > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    val resultsQ = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.qualifiedSucc.toDouble() } }.average()
      }
    }
    
    val results2Q = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.qualifiedSucc > 0 }.toDouble() }.average()
      }
    }
    
    val results3Q = names.map { name ->
      kList.sorted().map { k ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.filter { it.qualifiedSucc > 0 }.distinctBy { it.path.first() to it.path.last() }.size.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"throughput-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"succ-paths-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2}
        }""".trimIndent(), """
        {
          "name": "${"succ-pairs-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3}
        }""".trimIndent(),"""
        {
          "name": "${"qualified-throughput-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "Throughput (eps)",
          "y": ${resultsQ}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-paths-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ main paths",
          "y": ${results2Q}
        }""".trimIndent(), """
        {
          "name": "${"qualified-succ-pairs-$d-$n-$p-$q-k-$nsd".replace(".", "")}",
          "xTitle": "Link state broadcast range k",
          "x": ${listOf(0, 3, 6, 9)},
          "xTicks&Labels": [${listOf(0, 3, 6, 9)}, ["0", "3", "6", "∞"]],
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "yTitle": "# succ S-D pairs",
          "y": ${results3Q}
        }""".trimIndent()
    )
  }

  fun throughputFth() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val xs = fthList

    // Raw throughput (succ)
    val raw = names.map { name ->
      xs.map { fth ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        rlist.map { it.majorPaths.sumByDouble { mp -> mp.succ.toDouble() } }.average()
      }
    }

    // Qualified throughput (qualifiedSucc)
    val qualified = names.map { name ->
      xs.map { fth ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        rlist.map { it.majorPaths.sumByDouble { mp -> mp.qualifiedSucc.toDouble() } }.average()
      }
    }

    children += listOf(
      """
        {
          "name": "${"throughput-fth-$d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Fidelity threshold (F_th)",
          "yTitle": "Throughput (eps)",
          "x": $xs,
          "y": $raw
        }""".trimIndent(),
      """
        {
          "name": "${"qualified-throughput-fth-$d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Fidelity threshold (F_th)",
          "yTitle": "Qualified throughput (eps)",
          "x": $xs,
          "y": $qualified
        }""".trimIndent()
    )
  }
  
  fun efficiency() {
    (1..3).forEach { mode ->
      val names =
        if (mode == 1) listOf("Online", "SL", "Greedy_H", "CR")
        else if (mode == 2)
          listOf("Online", "SL", "Greedy_H")
        else listOf("Online", "Online-R", "CR", "CR-R")
      
      val (d, n, p, q, k, nsd) = referenceSetting
      val fth = 0.7
      var max = 0
      
      val channels = names.map { name ->
        val result = ReducibleLazyEvaluation<Int, Double>({ Double.NaN })
        
        topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }.map {
          it.majorPaths.sumBy { it.succ } to it.rpChannelCnt +
              it.majorPaths.sumBy { it.width * (it.path.size - 1) + it.recoveryPaths.sumBy { it.width * (it.path.size - 1) } }
        }.groupBy { it.first }.map {
          max = Math.max(max, it.key)
          result[it.key] = it.value.map { it.second.toDouble() }.average()
        }
        
        (0..max).map { result[it] }
      }
      
      children += """
        {
          "name": "${"channels-throughput-$d-$n-$p-$q-$k-$nsd${if (mode == 1) "" else if (mode == 2) "-noA1" else "-rp"}".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Throughput (eps)",
          "yTitle": "# occupied channels",
          "x": ${(0..max).toList()},
          "xTicks&Labels": ${(0..max).chunked(5).map { it.first() }},
          "y": ${channels.map { l -> if (l.size < max + 1) l + List(max + 1 - l.size, { Double.NaN }) else l }}
        }""".trimIndent()
    }
  }
  
  fun fairness() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    
    var max = 0
    
    val result = names.map { name ->
      var s = 0
      val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
      
      topoRange.flatMap { topoIdx ->
        parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
      }.flatMap { it.majorPaths.groupBy { it.path.first() to it.path.last() }.map { it.value.sumBy { it.width } } }
        .groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max = Math.max(max, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
      
      (0..max).map { sum[it] / s.toDouble() }
    }
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"mp-cdf-$d-$n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Total width of allocated major paths",
          "yTitle": "CDF",
          "xLimit": [0, $max],
          "yLimit": [0, 1],
          "x": ${(0..max).toList()},
          "y": ${result.map { l -> if (l.size < max + 1) l + List(max + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent()
    )
  }
  
  fun recovery1() {
    val q = qList.first()
    val k = kList.first()
    val d = dList.first()
    val fth = 0.7
    
    pList.forEach { p ->
      for (n in nList.sorted()) {
        var deviation = 0
        if (p != pList.first()) deviation++
        if (n != nList.first()) deviation++
        
        if (deviation >= 1) continue
        
        val names = listOf("CR", "CR-R")
        
        val results = names.map { name ->
          nsdList.sorted().map { nsd ->
            val rlist = topoRange.flatMap { topoIdx ->
              parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
            }
            
            rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
          }
        }
        
        val results2 = names.map { name ->
          nsdList.sorted().map { nsd ->
            val rlist = topoRange.flatMap { topoIdx ->
              parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
            }
            
            rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
          }
        }
        
        children += listOf(
          """
          {
            "name": "${"a1-rp-throughput-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
            "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
            "xTitle": "# S-D pairs in one time slot",
            "yTitle": "Throughput (eps)",
            "x": $nsdList,
            "y": ${results}
          }""".trimIndent(), """
          {
            "name": "${"a1-rp-succ-pairs-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
            "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
            "xTitle": "# S-D pairs in one time slot",
            "yTitle": "# succ S-D pairs",
            "x": $nsdList,
            "y": ${results2}
          }""".trimIndent()
        )
      }
    }
  }
  
  fun rp2Cdf_nsd() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    var max1 = 0
    val result1 =
      nsdList.sorted().map { nsd ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.flatMap { it.recoveryPaths.map { it.path.size - 1 } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max1 = Math.max(max1, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max1).map { sum[it] / s.toDouble() }
      }
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-len-cdf-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${nsdList.sorted().map { """ "$it S-D pair${if (it > 1) "s" else ""}" """ }},
          "legendColumn": 2,
          "legendFontSize": 10,
          "legendAutomaticallyReorder": false,
          "xTitle": "Length of recovery path",
          "yTitle": "CDF",
          "xLimit": [0, $max1],
          "yLimit": [0, 1],
          "x": ${(0..max1).toList()},
          "y": ${result1.map { l -> if (l.size < max1 + 1) l + List(max1 + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent()
    )
    
    var max2 = 0
    val result2 =
      nsdList.sorted().map { nsd ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.flatMap { it.recoveryPaths.map { it.width } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max2 = Math.max(max2, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max2).map { sum[it] / s.toDouble() }
      }
    
    max2 = result2.map { it.indexOfFirst { it > 0.99 } }.max()!!
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-wid-cdf-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${nsdList.sorted().map { """ "$it S-D pair${if (it > 1) "s" else ""}" """ }},
          "legendColumn": 2,
          "legendFontSize": 10,
          "legendAutomaticallyReorder": false,
          "xTitle": "Width of recovery path",
          "yTitle": "CDF",
          "xLimit": [0, $max2],
          "yLimit": [0, 1],
          "x": ${(0..max2).toList()},
          "y": ${result2.map { l -> if (l.size < max2 + 1) l + List(max2 + 1 - l.size, { 1.0 }) else l.take(max2 + 1) }}
        }""".trimIndent()
    )
    
    var max3 = 0
    val result3 =
      nsdList.sorted().map { nsd ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.map { it.recoveryPaths.sumBy { it.width } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max3 = Math.max(max3, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max3).map { sum[it] / s.toDouble() }
      }
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-wid-per-mp-cdf-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${nsdList.sorted().map { """ "$it S-D pair${if (it > 1) "s" else ""}" """ }},
          "legendColumn": 2,
          "legendFontSize": 10,
          "legendAutomaticallyReorder": false,
          "xTitle": "# recovery paths per major path",
          "yTitle": "CDF",
          "xLimit": [0, $max3],
          "yLimit": [0, 1],
          "x": ${(0..max3).toList()},
          "y": ${result3.map { l -> if (l.size < max3 + 1) l + List(max3 + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent()
    )
    
    var max = 0
    val names = listOf("Online", "Online-R", "CR", "CR-R")
    
    val result = names.map { name ->
      var s = 0
      val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
      
      topoRange.flatMap { topoIdx ->
        parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
      }.map { it.majorPaths.sumBy { it.succ } }.groupBy { it }.map { (k, v) ->
        k to v.size
      }.sortedBy { it.first }.forEach { (k, v) ->
        max = Math.max(max, k)
        s += v
        (k..1000).forEach { i -> sum[i] = s }
      }
      
      (0..max).map { sum[it] / s.toDouble() }
    }
    
    children.add(
      """
      {
        "markerSize": 0,
          "name": "${"rp-throughput-cdf-$d-$n-$p-$q-$k-$nsd".replace(".", "")}",
        "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
        "xTitle": "Throughput (eps)",
        "yTitle": "CDF",
        "xLimit": [0, $max],
        "yLimit": [0, 1],
        "x": ${(0..max).toList()},
          "xTicks&Labels": ${(0..max).chunked(5).map { it.first() }},
        "y": ${result.map { l -> if (l.size < max + 1) l + List(max + 1 - l.size, { 1.0 }) else l }}
      }""".trimIndent()
    )
  }
  
  fun rp2Cdf_n() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    var max1 = 0
    val result1 =
      nList.sorted().map { n ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.flatMap { it.recoveryPaths.map { it.path.size - 1 } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max1 = Math.max(max1, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max1).map { sum[it] / s.toDouble() }
      }
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-len-cdf-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${nList.sorted().map { """ "|V| = $it" """ }},
          "xTitle": "Length of recovery path",
          "yTitle": "CDF",
          "xLimit": [0, $max1],
          "yLimit": [0, 1],
          "x": ${(0..max1).toList()},
          "y": ${result1.map { l -> if (l.size < max1 + 1) l + List(max1 + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent()
    )
    
    var max2 = 0
    val result2 =
      nList.sorted().map { n ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.flatMap { it.recoveryPaths.map { it.width } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max2 = Math.max(max2, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max2).map { sum[it] / s.toDouble() }
      }
    
    max2 = result2.map { it.indexOfFirst { it > 0.99 } }.max()!!
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-wid-cdf-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${nList.sorted().map { """ "|V| = $it" """ }},
          "xTitle": "Width of recovery path",
          "yTitle": "CDF",
          "xLimit": [0, $max2],
          "yLimit": [0, 1],
          "x": ${(0..max2).toList()},
          "y": ${result2.map { l -> if (l.size < max2 + 1) l + List(max2 + 1 - l.size, { 1.0 }) else l.take(max2 + 1) }}
        }""".trimIndent()
    )
    
    var max3 = 0
    val result3 =
      nList.sorted().map { n ->
        var s = 0
        val sum = ReducibleLazyEvaluation<Int, Int>({ 0 })
        
        val y = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, "Online", fth) + ".txt")
        }.flatMap { it.majorPaths.map { it.recoveryPaths.sumBy { it.width } } }
        
        y.groupBy { it }.map { (k, v) -> k to v.size }.sortedBy { it.first }.forEach { (k, v) ->
          max3 = Math.max(max3, k)
          s += v
          (k..1000).forEach { i -> sum[i] = s }
        }
        
        (0..max3).map { sum[it] / s.toDouble() }
      }
    
    children.add(
      """
        {
          "markerSize": 0,
          "name": "${"a2-rp-wid-per-mp-cdf-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${nList.sorted().map { """ "|V| = $it" """ }},
          "xTitle": "# recovery paths per major path",
          "yTitle": "CDF",
          "xLimit": [0, $max3],
          "yLimit": [0, 1],
          "x": ${(0..max3).toList()},
          "y": ${result3.map { l -> if (l.size < max3 + 1) l + List(max3 + 1 - l.size, { 1.0 }) else l }}
        }""".trimIndent()
    )
  }
  
  fun rp2Nsd() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    val names = listOf("Online", "Online-R")
    
    val results = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      nsdList.sorted().map { nsd ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"a2-rp-throughput-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "Throughput (eps)",
          "x": ${nsdList},
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"a2-rp-succ-pairs-$d-$n-$p-$q-$k-nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "# S-D pairs in one time slot",
          "yTitle": "Success S-D pairs",
          "x": ${nsdList},
          "y": ${results2}
        }""".trimIndent()
    )
  }
  
  fun rp2N() {
    val (d, n, p, q, k, nsd) = referenceSetting
    val fth = 0.7
    
    val names = listOf("Online", "Online-R")
    
    val results = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.sumByDouble { it.succ.toDouble() } }.average()
      }
    }
    
    val results2 = names.map { name ->
      nList.sorted().map { n ->
        val rlist = topoRange.flatMap { topoIdx ->
          parseLog("dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt")
        }
        
        rlist.map { it.majorPaths.count { it.succ > 0 }.toDouble() }.average()
      }
    }
    
    children += listOf(
      """
        {
          "name": "${"a2-rp-throughput-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "Throughput (eps)",
          "x": ${nList.sorted()},
          "y": ${results}
        }""".trimIndent(), """
        {
          "name": "${"a2-rp-succ-pairs-$d-n-$p-$q-$k-$nsd".replace(".", "")}",
          "solutionList": ${names.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "|V|",
          "xLog" : true,
          "xTicks&Labels": [${nList.sorted()}, ${nList.sorted().map { """ "$it" """ }}],
          "yTitle": "Success S-D pairs",
          "x": ${nList.sorted()},
          "y": ${results2}
        }""".trimIndent()
    )
  }

  // --- Topology parser: extracts shortest-path hops from log file ---

  private data class TopoInfo(
      val hopDist: Array<IntArray>,
      val nodeLocs: Array<DoubleArray>
  )

  private fun parseTopologyFromLog(fn: String): TopoInfo? {
    try {
      val allLines = File(fn).readLines()
      val sepIdx = allLines.indexOfFirst { it.startsWith("---") }
      if (sepIdx < 0) return null

      val topoLines = allLines.subList(sepIdx + 1, allLines.size)

      val nTopo = topoLines[0].trim().toIntOrNull() ?: return null

      val nodeLocs = Array(nTopo) { i ->
        val toks = topoLines[4 + i].trim().split(Regex("\\s+"))
        doubleArrayOf(toks[1].toDouble(), toks[2].toDouble())
      }

      val adj = Array(nTopo) { mutableSetOf<Int>() }
      var lineIdx = 4 + nTopo
      while (lineIdx < topoLines.size) {
        val line = topoLines[lineIdx].trim()
        if (line.isEmpty() || !line[0].isDigit()) break
        val toks = line.split(Regex("\\s+"))
        if (toks.size < 3) break
        try {
          val u = toks[0].toInt()
          val v = toks[1].toInt()
          adj[u].add(v)
          adj[v].add(u)
        } catch (e: Exception) { break }
        lineIdx++
      }

      // All-pairs BFS for shortest-path hop counts
      val dist = Array(nTopo) { IntArray(nTopo) { Int.MAX_VALUE } }
      for (src in 0 until nTopo) {
        dist[src][src] = 0
        val queue = java.util.LinkedList<Int>()
        queue.add(src)
        while (queue.isNotEmpty()) {
          val u = queue.poll()
          for (v in adj[u]) {
            if (dist[src][v] == Int.MAX_VALUE) {
              dist[src][v] = dist[src][u] + 1
              queue.add(v)
            }
          }
        }
      }

      return TopoInfo(dist, nodeLocs)
    } catch (e: Exception) {
      println("Error parsing topology from $fn: ${e.message}")
      return null
    }
  }

  // --- Range analysis: success rate & throughput vs hop distance ---

  fun rangeAnalysis() {
    val (d, n, p, q, k, _) = referenceSetting
    val nsd = 1
    val fth = 0.70

    // Parse topology from any log file (same for all algorithms)
    val sampleFn = "dist/" + id(n, 1, q, k, p, d, nsd, names.first(), fth) + ".txt"
    val topoInfo = parseTopologyFromLog(sampleFn)
    if (topoInfo == null) {
      println("could not parse topology from $sampleFn — skipping rangeAnalysis")
      return
    }
    val hopDist = topoInfo.hopDist

    val maxHop = 15
    val minSamples = 10

    // Collect per-hop-bin data for each algorithm
    data class BinData(
        val servedRaw: MutableList<Boolean> = mutableListOf(),
        val servedQualified: MutableList<Boolean> = mutableListOf(),
        val rawCount: MutableList<Int> = mutableListOf(),
        val qualifiedCount: MutableList<Int> = mutableListOf()
    )

    val algData = names.map { name ->
      val bins = Array(maxHop + 1) { BinData() }

      topoRange.flatMap { topoIdx ->
        val fn = "dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt"
        if (!File(fn).exists()) {
          println("MISSING: $fn")
          return@flatMap emptyList<Record>()
        }
        parseLog(fn)
      }.forEach { record ->
        if (record.ops.size == 1) {
          val (src, dst) = record.ops[0]
          val h = hopDist[src][dst]
          if (h in 1..maxHop) {
            val totalRaw = record.majorPaths.sumBy { it.succ }
            val totalQ = record.majorPaths.sumBy { it.qualifiedSucc }
            bins[h].servedRaw.add(totalRaw > 0)
            bins[h].servedQualified.add(totalQ > 0)
            bins[h].rawCount.add(totalRaw)
            bins[h].qualifiedCount.add(totalQ)
          }
        }
      }
      bins
    }

    // Print sample counts per hop for verification
    println("=== Range Analysis: sample counts per hop (nsd=$nsd, fth=$fth) ===")
    (1..maxHop).forEach { h ->
      val counts = algData.mapIndexed { i, bins -> "${names[i]}=${bins[h].servedRaw.size}" }
      if (algData.any { it[h].servedRaw.isNotEmpty() }) {
        println("  hop $h: ${counts.joinToString(", ")}")
      }
    }

    // Filter to algorithms that have data, and hops where at least one has enough samples
    val activeAlgIndices = names.indices.filter { i ->
      algData[i].any { bin -> bin.servedRaw.size >= minSamples }
    }
    if (activeAlgIndices.isEmpty()) {
      println("no algorithms have >= $minSamples samples in any hop bin")
      return
    }

    val activeNames = activeAlgIndices.map { names[it] }
    println("Active algorithms: $activeNames")

    val validHops = (1..maxHop).filter { h ->
      activeAlgIndices.all { i -> algData[i][h].servedRaw.size >= minSamples }
    }

    if (validHops.isEmpty()) {
      println("no hop bins with >= $minSamples samples for all active algorithms")
      return
    }

    println("Valid hops for plotting: $validHops")

    val activeAlgData = activeAlgIndices.map { algData[it] }

    // Qualified success rate by hop
    val qualifiedSuccessRates = activeAlgData.map { bins ->
      validHops.map { h ->
        bins[h].servedQualified.count { it }.toDouble() / bins[h].servedQualified.size
      }
    }

    // Raw success rate by hop
    val rawSuccessRates = activeAlgData.map { bins ->
      validHops.map { h ->
        bins[h].servedRaw.count { it }.toDouble() / bins[h].servedRaw.size
      }
    }

    // Avg qualified throughput by hop
    val avgQualifiedThroughput = activeAlgData.map { bins ->
      validHops.map { h ->
        bins[h].qualifiedCount.map { it.toDouble() }.average()
      }
    }

    // Avg raw throughput by hop
    val avgRawThroughput = activeAlgData.map { bins ->
      validHops.map { h ->
        bins[h].rawCount.map { it.toDouble() }.average()
      }
    }

    children += listOf(
      """
        {
          "name": "range-qualified-success-rate-by-hop",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Shortest-path hop count",
          "yTitle": "P(pair served with qualified ebit)",
          "x": $validHops,
          "y": $qualifiedSuccessRates,
          "yLimit": [0, 1.05]
        }""".trimIndent(),
      """
        {
          "name": "range-raw-success-rate-by-hop",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Shortest-path hop count",
          "yTitle": "P(pair served with any ebit)",
          "x": $validHops,
          "y": $rawSuccessRates,
          "yLimit": [0, 1.05]
        }""".trimIndent(),
      """
        {
          "name": "range-qualified-throughput-by-hop",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Shortest-path hop count",
          "yTitle": "Avg qualified throughput (eps)",
          "x": $validHops,
          "y": $avgQualifiedThroughput
        }""".trimIndent(),
      """
        {
          "name": "range-raw-throughput-by-hop",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Shortest-path hop count",
          "yTitle": "Avg raw throughput (eps)",
          "x": $validHops,
          "y": $avgRawThroughput
        }""".trimIndent()
    )
  }

  // --- Range analysis by Euclidean distance ---

  fun rangeAnalysisByDistance() {
    val (d, n, p, q, k, _) = referenceSetting
    val nsd = 1
    val fth = 0.70

    val sampleFn = "dist/" + id(n, 1, q, k, p, d, nsd, names.first(), fth) + ".txt"
    val topoInfo = parseTopologyFromLog(sampleFn)
    if (topoInfo == null) {
      println("WARNING: could not parse topology from $sampleFn — skipping rangeAnalysisByDistance")
      return
    }
    val nodeLocs = topoInfo.nodeLocs

    fun euclidean(a: Int, b: Int): Double {
      val dx = nodeLocs[a][0] - nodeLocs[b][0]
      val dy = nodeLocs[a][1] - nodeLocs[b][1]
      return Math.sqrt(dx * dx + dy * dy)
    }

    // Determine bin edges from the actual distance distribution
    val allDists = mutableListOf<Double>()
    topoRange.flatMap { topoIdx ->
      val fn = "dist/" + id(n, topoIdx, q, k, p, d, nsd, names.first(), fth) + ".txt"
      if (!File(fn).exists()) return@flatMap emptyList<Record>()
      parseLog(fn)
    }.forEach { record ->
      if (record.ops.size == 1) {
        val (src, dst) = record.ops[0]
        allDists.add(euclidean(src, dst))
      }
    }

    if (allDists.isEmpty()) {
      println("no data for distance analysis")
      return
    }

    val maxDist = allDists.max()!!
    val binWidth = 5.0
    val numBins = (maxDist / binWidth).toInt() + 1
    val minSamples = 10

    println("=== Range Analysis by Distance (nsd=$nsd, fth=$fth) ===")
    println("  Max Euclidean distance: ${"%.1f".format(maxDist)}, bin width: $binWidth, bins: $numBins")

    data class BinData(
        val servedRaw: MutableList<Boolean> = mutableListOf(),
        val servedQualified: MutableList<Boolean> = mutableListOf(),
        val rawCount: MutableList<Int> = mutableListOf(),
        val qualifiedCount: MutableList<Int> = mutableListOf()
    )

    fun binIndex(dist: Double): Int = (dist / binWidth).toInt().coerceIn(0, numBins - 1)
    fun binCenter(idx: Int): Double = idx * binWidth + binWidth / 2.0

    // Filter to active algorithms
    val algBins = names.map { name ->
      val bins = Array(numBins) { BinData() }

      topoRange.flatMap { topoIdx ->
        val fn = "dist/" + id(n, topoIdx, q, k, p, d, nsd, name, fth) + ".txt"
        if (!File(fn).exists()) {
          println("MISSING: $fn")
          return@flatMap emptyList<Record>()
        }
        parseLog(fn)
      }.forEach { record ->
        if (record.ops.size == 1) {
          val (src, dst) = record.ops[0]
          val dist = euclidean(src, dst)
          val b = binIndex(dist)
          val totalRaw = record.majorPaths.sumBy { it.succ }
          val totalQ = record.majorPaths.sumBy { it.qualifiedSucc }
          bins[b].servedRaw.add(totalRaw > 0)
          bins[b].servedQualified.add(totalQ > 0)
          bins[b].rawCount.add(totalRaw)
          bins[b].qualifiedCount.add(totalQ)
        }
      }
      bins
    }

    val activeAlgIndices = names.indices.filter { i ->
      algBins[i].any { bin -> bin.servedRaw.size >= minSamples }
    }
    if (activeAlgIndices.isEmpty()) {
      println("no algorithms have >= $minSamples samples in any distance bin")
      return
    }

    val activeNames = activeAlgIndices.map { names[it] }
    val activeAlgBins = activeAlgIndices.map { algBins[it] }

    val validBinIndices = (0 until numBins).filter { b ->
      activeAlgBins.all { it[b].servedRaw.size >= minSamples }
    }

    if (validBinIndices.isEmpty()) {
      println("no distance bins with >= $minSamples samples for all active algorithms")
      return
    }

    val xs = validBinIndices.map { binCenter(it) }

    // Print sample counts
    for (b in validBinIndices) {
      val lo = b * binWidth
      val hi = lo + binWidth
      val counts = activeAlgIndices.mapIndexed { i, ai -> "${names[ai]}=${algBins[ai][b].servedRaw.size}" }
      println("  [${"%5.1f".format(lo)}, ${"%5.1f".format(hi)}): ${counts.joinToString(", ")}")
    }

    println("Active algorithms: $activeNames")
    println("Valid distance bins: ${validBinIndices.size}")

    val qualifiedSuccessRates = activeAlgBins.map { bins ->
      validBinIndices.map { b ->
        bins[b].servedQualified.count { it }.toDouble() / bins[b].servedQualified.size
      }
    }

    val rawSuccessRates = activeAlgBins.map { bins ->
      validBinIndices.map { b ->
        bins[b].servedRaw.count { it }.toDouble() / bins[b].servedRaw.size
      }
    }

    val avgQualifiedThroughput = activeAlgBins.map { bins ->
      validBinIndices.map { b ->
        bins[b].qualifiedCount.map { it.toDouble() }.average()
      }
    }

    val avgRawThroughput = activeAlgBins.map { bins ->
      validBinIndices.map { b ->
        bins[b].rawCount.map { it.toDouble() }.average()
      }
    }

    children += listOf(
      """
        {
          "name": "range-qualified-success-rate-by-distance",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Euclidean S-D distance (km)",
          "yTitle": "P(pair served with qualified ebit)",
          "x": $xs,
          "y": $qualifiedSuccessRates,
          "yLimit": [0, 1.05]
        }""".trimIndent(),
      """
        {
          "name": "range-raw-success-rate-by-distance",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Euclidean S-D distance (km)",
          "yTitle": "P(pair served with any ebit)",
          "x": $xs,
          "y": $rawSuccessRates,
          "yLimit": [0, 1.05]
        }""".trimIndent(),
      """
        {
          "name": "range-qualified-throughput-by-distance",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Euclidean S-D distance (km)",
          "yTitle": "Avg qualified throughput (eps)",
          "x": $xs,
          "y": $avgQualifiedThroughput
        }""".trimIndent(),
      """
        {
          "name": "range-raw-throughput-by-distance",
          "solutionList": ${activeNames.map { """ "${nameMapping[it] ?: it}" """ }},
          "xTitle": "Euclidean S-D distance (km)",
          "yTitle": "Avg raw throughput (eps)",
          "x": $xs,
          "y": $avgRawThroughput
        }""".trimIndent()
    )
  }
  
  companion object {
    @JvmStatic
    fun main(args: Array<String>) {
      val p = Plot()
      
      p.throughputCdf()
      
      p.throughputD()
      p.throughputK()
      p.throughputN()
      p.throughputNsd()
      p.throughputP()
      p.throughputQ()
      p.throughputFth()

      p.rangeAnalysis()
      p.rangeAnalysisByDistance()
      
      // p.efficiency()
      // p.fairness()
      // p.recovery1()
      
      // p.rp2Cdf_nsd()
      // p.rp2Cdf_n()
      // p.rp2N()
      // p.rp2Nsd()
      
      p.plot()
    }
  }
}
