package util


/**
 * A core warning printer.
 * The inner core of the application (no user interface loaded can emit warnings this way.
 * The user interface may override the print_function such that the warning are 
 * consistent with the user interface.
 */
object WarningPrinter {
  
  //a function to print errors
  var print_function: (String) => Unit = null
  
  //default function: print to stdio
  print_function = {err => println("WARNING: "+err)}
  
  def emit_warning(warn: String) = print_function(warn)

}