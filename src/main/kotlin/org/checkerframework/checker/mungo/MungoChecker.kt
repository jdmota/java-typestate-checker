package org.checkerframework.checker.mungo

import org.checkerframework.checker.mungo.typecheck.Typechecker
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.source.SourceVisitor
import java.io.IOException
import java.util.*
import javax.tools.Diagnostic

const val showTypeInfoOpt = "showTypeInfo"
const val configFileOpt = "configFile"
const val messagesFile = "/messages.properties"

class MungoChecker : SourceChecker() {

  lateinit var utils: MungoUtils

  override fun getSupportedOptions() = super.getSupportedOptions().plus(showTypeInfoOpt).plus(configFileOpt)

  fun shouldReportTypeInfo() = hasOption(showTypeInfoOpt)

  override fun createSourceVisitor(): SourceVisitor<*, *> {
    return Typechecker(this)
  }

  override fun initChecker() {
    super.initChecker()
    val utils = MungoUtils(this)
    utils.initFactory()
    this.utils = utils
  }

  private fun getProperties(): Properties {
    val prop = Properties()
    try {
      val stream = javaClass.getResourceAsStream(messagesFile)
      prop.load(stream)
    } catch (e: IOException) {
      message(Diagnostic.Kind.WARNING, "Couldn't parse properties file: $messagesFile")
    }
    return prop
  }

  override fun getMessagesProperties(): Properties {
    return if (messagesProperties != null) {
      messagesProperties
    } else {
      messagesProperties = Properties()
      messagesProperties.putAll(getProperties())
      messagesProperties
    }
  }

}
