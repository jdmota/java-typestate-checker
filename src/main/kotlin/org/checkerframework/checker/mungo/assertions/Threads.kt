package org.checkerframework.checker.mungo.assertions

import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.utils.MungoUtils
import java.nio.file.Paths

val threadProtocol = """
  typestate JavaThread {
    NotStarted = {
      void start(): Started
    }
    Started = {
      void join(): end
    }
  }
""".trimIndent()

class LambdaThread private constructor(val lambda: JCTree.JCLambda, val graph: Graph) {

  companion object {
    private var uuid = 1L

    fun create(utils: MungoUtils, lambda: JCTree.JCLambda): LambdaThread {
      val id = uuid++
      val graph = TypestateProcessor.fromString(utils, threadProtocol, Paths.get("java_thread_$id.protocol"))
      return LambdaThread(lambda, graph!!)
    }
  }

}
