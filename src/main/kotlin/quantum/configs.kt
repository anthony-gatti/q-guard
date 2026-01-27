package quantum

import utils.ReducibleLazyEvaluation
import utils.Tuple
import utils.toPair
import java.io.File
import java.util.*

//val randGen = Random((Math.random() * Long.MAX_VALUE).toLong())
val randGen = Random(19900111L)

val edgeLen = 100.0
val maxSearchHops = 15

var nList = listOf(200, 50, 200, 400, 800)
val dList = listOf(6, 5, 4, 3)
val kList = listOf(3, 6, 0, 10000)
val qList = listOf(0.9, 0.8, 0.85, 0.95, 1.0)
val pList = listOf(0.7, 0.5, 0.6, 0.8, 0.9, 1.0)
val nsdList = (1..10).toList()
val topoRange = (1..1).toList()
val fthList = listOf(
  0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90, 0.95
)


val allAvailableSettings =
  dList.flatMap { d ->
    pList.flatMap { p ->
      nList.flatMap { n ->
        qList.flatMap { q ->
          kList.flatMap { k ->
            nsdList.flatMap { nsd ->
              var deviation = 0
              if (k != kList.first()) deviation++
              if (d != dList.first()) deviation++
              if (q != qList.first()) deviation++
              if (p != pList.first()) deviation++
              if (n != nList.first()) deviation++
              if (nsd != nsdList.last()) deviation++
              
              if (deviation > 1) listOf()
              else listOf(Tuple(d, n, p, q, k, nsd))
            }
          }
        }
      }
    }
  }

val referenceSetting = Tuple(dList.first(), nList.first(), pList.first(), qList.first(), kList.first(), nsdList.last())

fun id(n: Int, topoIdx: Int, q: Double, k: Int, p: Double, d: Int, numPairs: Int, name: String, fth: Double): String {
  val fthTag = String.format(Locale.US, "%.2f", fth)
  return """$n#$topoIdx-$q-$k-$p-$d-$numPairs-fth$fthTag-${name}"""
}

val records = ReducibleLazyEvaluation<String, MutableList<Record>>({ mutableListOf() })

enum class Type { Online, Offline }
data class RecoveryPath2(val path: IntArray, val width: Int, val good: Int, val taken: Int)
data class RecoveryPath1(val path: IntArray, val occupiedChannels: Int, val goodChannels: Int)
data class MajorPath(val path: IntArray, val width: Int, val succ: Int, val type: Type, val recoveryPaths: MutableList<RecoveryPath2>, val qualifiedSucc: Int)
data class Record(val ops: List<Pair<Int, Int>>, val majorPaths: MutableList<MajorPath>, var rpCnt: Int, var rpChannelCnt: Int)

// fun parseLog(fn: String): List<Record> {
//   val f = File(fn)
//   if (records[f.nameWithoutExtension].isEmpty()) try {
//     var currRecord = null as Record?
//     var currMajorPath = null as MajorPath?
    
//     for (line in f.readLines()) {
//       if (line.startsWith("-----")) continue
//       if (line.trim().isEmpty()) continue
//       try {
//         val indent = line.takeWhile { it == ' ' }.length
//         if (indent == 0) {
//           currMajorPath = null
//           if (currRecord != null) {
//             records[f.nameWithoutExtension].add(currRecord)
//           }
//           currRecord = Record(line.split(Regex("""[^\d]+""")).map { it.toInt() }.chunked(2).map { it.toPair() }, mutableListOf(), 0, 0)
//         } else if (indent == 1) {
//           if (line.contains("recovery")) {
//             val seg = line.trim().split(Regex("""[^\d]+""")).drop(1).dropLast(1)
//             val (taken) = seg.takeLast(1).map { it.toInt() }
//             currRecord!!.rpCnt += 1
//             currRecord!!.rpChannelCnt += taken
//           } else {
//             if (!line.contains("[") || !line.contains("],")) throw Exception("incomplete")
//             var l = line
            
//             var type = Type.Online
//             if (line.contains("//")) {
//               if (line.contains("offline")) type = Type.Offline
              
//               l = line.split("//")[0].trim()
//             }
            
//             val seg = l.trim().split(Regex("""[^\d]+""")).drop(1)
//             val (width, succ) = seg.takeLast(2).map { it.toInt() }
            
//             currMajorPath = MajorPath(seg.dropLast(2).map { it.toInt() }.toIntArray(), width, succ, type, mutableListOf())
//             if (currMajorPath.path.first() to currMajorPath.path.last() !in currRecord!!.ops) throw Exception("incomplete")
//             currRecord.majorPaths.add(currMajorPath)
//           }
//         } else {
//           val seg = line.trim().split(Regex("""[^\d]+""")).drop(1)
//           val (width, succ, taken) = seg.takeLast(3).map { it.toInt() }
          
//           currMajorPath!!.recoveryPaths.add(RecoveryPath2(seg.dropLast(3).map { it.toInt() }.toIntArray(), width, succ, taken))
//         }
//       } catch (e: Exception) {
//         currRecord = null
//         currMajorPath = null
//       }
//     }
//   } catch (e: Exception) {
//   }
//   return records[f.nameWithoutExtension]
// }

fun parseLog(fn: String): List<Record> {
  val f = File(fn)
  if (records[f.nameWithoutExtension].isEmpty()) try {
    var currRecord: Record? = null
    var currMajorPath: MajorPath? = null

    for (rawLine in f.readLines()) {
      if (rawLine.startsWith("-----")) continue
      if (rawLine.trim().isEmpty()) continue

      val line = rawLine
      val indent = line.takeWhile { it == ' ' }.length

      try {
        if (indent == 0) {
          // Header line should contain S-D pairs with "⟷"
          if (!line.contains("⟷")) {
            // e.g., "PRED ..." or other debug; ignore
            continue
          }

          currMajorPath = null
          if (currRecord != null) {
            records[f.nameWithoutExtension].add(currRecord)
          }

          val opsInts = line.split(Regex("""[^\d]+"""))
            .filter { it.isNotEmpty() }
            .map { it.toInt() }

          val opsPairs = opsInts.chunked(2).map { it.toPair() }
          currRecord = Record(opsPairs, mutableListOf(), 0, 0)

        } else if (indent == 1) {
          // indent=1: either a major path line or some other debug line
          if (line.contains("recovery")) {
            // Original recovery summary line
            val seg = line.trim().split(Regex("""[^\d]+""")).drop(1).dropLast(1)
            val (taken) = seg.takeLast(1).map { it.toInt() }
            currRecord!!.rpCnt += 1
            currRecord!!.rpChannelCnt += taken
          } else {
            // We only care about lines that actually contain a "[...]" path
            if (!line.contains("[") || !line.contains("]")) {
              // e.g., "EXG-SKIP ..." — ignore
              continue
            }

            var l = line

            var type = Type.Online
            if (line.contains("//")) {
              if (line.contains("offline")) type = Type.Offline
              l = line.split("//")[0].trim()
            }

            val trimmed = l.trim()
            val pathPart = trimmed.substringAfter("[").substringBefore("]")
            val metricsPart = trimmed.substringAfter("],").trim()

            val pathInts = pathPart.split(Regex("""[^\d]+"""))
              .filter { it.isNotEmpty() }
              .map { it.toInt() }

            val metricTokens = metricsPart.split(Regex("""\s+"""))
              .filter { it.isNotEmpty() }

            if (metricTokens.size < 2) throw Exception("incomplete metrics")

            // First token is always width
            val width = metricTokens[0].toInt()

            // Old format: width succ
            // New format: width rawSucc estF qualifiedSucc
            val (succ, qualifiedSucc) = if (metricTokens.size >= 4) {
                val rawSucc = metricTokens[1].toInt()
                val qSucc   = metricTokens[3].toInt()
                rawSucc to qSucc
            } else {
                val rawSucc = metricTokens[1].toInt()
                // For old logs with no fidelity info, you can either treat all succ as qualified…
                rawSucc to rawSucc
            }

            currMajorPath = MajorPath(pathInts.toIntArray(), width, succ, type, mutableListOf(), qualifiedSucc)
            if (currRecord == null ||
              currMajorPath.path.first() to currMajorPath.path.last() !in currRecord.ops
            ) {
              throw Exception("incomplete record")
            }
            currRecord.majorPaths.add(currMajorPath)
          }

        } else {
          // Recovery path line (indent > 1)
          // Format remains: [path], width succ taken
          if (!line.contains("[")) {
            // ignore any deeply-indented debug lines
            continue
          }

          val seg = line.trim().split(Regex("""[^\d]+""")).drop(1)
          val (width, succ, taken) = seg.takeLast(3).map { it.toInt() }

          val pathInts = seg.dropLast(3).map { it.toInt() }.toIntArray()
          currMajorPath!!.recoveryPaths.add(
            RecoveryPath2(pathInts, width, succ, taken)
          )
        }
      } catch (e: Exception) {
        // If a line is malformed, just reset state and continue
        currRecord = null
        currMajorPath = null
      }
    }

  } catch (e: Exception) {
    // swallow file-level exceptions and just return what we have
  }

  return records[f.nameWithoutExtension]
}