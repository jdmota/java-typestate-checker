package org.checkerframework.checker.mungo.utils

import java.io.FileInputStream
import java.io.IOException
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*

class ConfigUtils(sourcePath: String?) {

  private val configName = "mungo.config"
  private val rootConfigFile: Path = if (sourcePath == null) MungoUtils.cwd.resolve(configName) else Paths.get(sourcePath).toAbsolutePath()

  private val emptyConfig = MungoConfig(mapOf())

  class MungoConfig(private val map: Map<String, Path>) {
    fun getProtocol(qualifiedName: String): Path? {
      return map[qualifiedName]
    }
  }

  private val configs = mutableMapOf<Path, Optional<MungoConfig>>()

  private fun createConfig(f: Path): MungoConfig? {
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
        Optional.of(MungoConfig(map))
      } catch (ex: IOException) {
        Optional.empty()
      }
    }.orElse(null)
  }

  fun getConfig() = createConfig(rootConfigFile) ?: emptyConfig

}
