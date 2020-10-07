// DESCRIPTION: check ROOT files of AFP sessions

object AFP_Check_Roots extends isabelle.Isabelle_Tool.Body {

  import isabelle._

  val afp_dir = Path.explode("$AFP").expand
  val excludes = List("ROOTS", "LICENSE", "LICENSE.LGPL", ".DS_Store")

  def print_good(string: String): Unit =
    println(Console.BOLD + Console.GREEN + string + Console.RESET)

  def print_bad(string: String): Unit =
    println(Console.BOLD + Console.RED + string + Console.RESET)

  class Check[T](
    run: (Sessions.Structure, List[String]) => List[T],
    failure_msg: String,
    failure_format: T => String)
  {
    def apply(tree: Sessions.Structure, selected: List[String]): Boolean =
      run(tree, selected) match {
        case Nil =>
          true
        case offenders =>
          print_bad(failure_msg)
          offenders.foreach(offender => println("  " + failure_format(offender)))
          false
      }
  }

  val check_timeout = new Check[(String, List[String])](
    run = { (tree, selected) =>
      selected.flatMap { name =>
        val info = tree(name)
        val entry = info.dir.base.implode
        val timeout = info.options.real("timeout")
        if (timeout == 0 || timeout % 300 != 0)
          Some((entry, name))
        else
          None
      }.groupBy(_._1).mapValues(_.map(_._2)).toList
    },
    failure_msg = "The following entries contain sessions without timeouts or with timeouts not divisible by 300:",
    failure_format = { case (entry, sessions) => s"""$entry ${sessions.mkString("(", ", ", ")")}""" }
  )

  val check_paths = new Check[(String, Path)](
    run = { (tree, selected) =>
      selected.flatMap { name =>
        val info = tree(name)
        val dir = info.dir
        if (dir.dir.expand.file != afp_dir.file)
          Some((name, dir))
        else
          None
      }
    },
    failure_msg = "The following sessions are in the wrong directory:",
    failure_format = { case (session, dir) => s"""$session ($dir)""" }
  )

  val check_chapter = new Check[String](
    run = { (tree, selected) =>
      selected.flatMap { name =>
        val info = tree(name)
        val entry = info.dir.base.implode
        if (info.chapter != "AFP")
          Some(entry)
        else
          None
      }.distinct
    },
    failure_msg = "The following entries are not in the AFP chapter:",
    failure_format = identity
  )

  val check_groups = new Check[(String, List[String])](
    run = { (tree, selected) =>
      selected.flatMap { name =>
        val info = tree(name)
        if (!info.groups.toSet.subsetOf(AFP.groups.keySet + "AFP") ||
            !info.groups.contains("AFP"))
          Some((name, info.groups))
        else
          None
      }
    },
    failure_msg = "The following sessions have wrong groups:",
    failure_format = { case (session, groups) => s"""$session ${groups.mkString("{", ", ", "}")}""" }
  )

  val check_presence = new Check[String](
    run = { (tree, selected) =>
      val fs_entries = File.read_dir(afp_dir).filterNot(excludes.contains)

      fs_entries.flatMap { name =>
        if (!selected.contains(name) || tree(name).dir.base.implode != name)
          Some(name)
        else
          None
      }
    },
    failure_msg = "The following entries (according to the file system) are not registered in ROOTS, or registered in the wrong ROOT:",
    failure_format = identity
  )

  def apply(args: List[String]): Unit =
  {
    val full_tree = Sessions.load_structure(Options.init(), Nil, List(afp_dir))
    val selected = full_tree.build_selection(Sessions.Selection.empty)

    val checks = List(
      check_timeout,
      check_paths,
      check_chapter,
      check_groups,
      check_presence)

    val bad = checks.exists(check => !check(full_tree, selected))

    if (bad)
    {
      print_bad("Errors found.")
      System.exit(1)
    }
    else
    {
      print_good(s"${selected.length} sessions have been checked")
      print_good(s"${checks.length} checks have found no errors")
    }
  }

}
