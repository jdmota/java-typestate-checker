package jatyc.utils

import jatyc.configFileOpt
import org.checkerframework.framework.source.SourceChecker
import java.io.FileInputStream
import java.io.IOException
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*

class ConfigUtils(checker: SourceChecker) {

  private val sourcePath: String? = checker.getOption(configFileOpt, null)
  private val configName = "jtc.config"
  private val rootConfigFile: Path = if (sourcePath == null) JTCUtils.cwd.resolve(configName) else Paths.get(sourcePath).toAbsolutePath()

  private val emptyConfig = JTCConfig(mapOf())

  class JTCConfig(private val map: Map<String, Path>) {
    fun getProtocol(qualifiedName: String): Path? {
      return map[qualifiedName]
    }
  }

  private val configs = mutableMapOf<Path, Optional<JTCConfig>>()

  private fun createConfig(f: Path): JTCConfig? {
    return configs.computeIfAbsent(f) { file ->
      val props = Properties()
      val map = mutableMapOf<String, Path>()
      try {
        props.load(FileInputStream(file.toFile()))
        for ((a, b) in props) {
          val key = (a as String).trim()
          val value = (b as String).trim()
          if (key.isNotEmpty()) {
            map[key] = file.resolveSibling(value).toAbsolutePath()
          }
        }
        Optional.of(JTCConfig(map))
      } catch (ex: IOException) {
        Optional.empty()
      }
    }.orElse(null)
  }

  fun getConfig() = createConfig(rootConfigFile) ?: emptyConfig

}
