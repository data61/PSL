// DESCRIPTION: extract dependencies between AFP entries

object AFP_Dependencies extends isabelle.Isabelle_Tool.Body {

  import isabelle._

  val afp_dir = Path.explode("$AFP").expand

  val tree = Sessions.load_structure(Options.init(), Nil, List(afp_dir))
  val selected = tree.selection(Sessions.Selection(false, false, Nil, Nil, Nil, Nil)).build_graph.keys

  def get_entry(name: String): Option[String] =
  {
    val info = tree(name)
    val dir = info.dir

    if (dir.dir.expand.file != afp_dir.file)
      None
    else
      Some(dir.base.implode)
  }

  def as_json(entry: String, distrib_deps: List[String], afp_deps: List[String]): String =
    s"""
      {"$entry":
        {"distrib_deps": [${commas_quote(distrib_deps)}],
         "afp_deps": [${commas_quote(afp_deps)}]
        }
      }"""

  def apply(args: List[String]): Unit =
  {
    val result = selected.groupBy(get_entry).collect {
      case (Some(e), sessions) =>
        val dependencies = sessions.flatMap(tree.imports_graph.imm_preds).map(d => (d, get_entry(d)))
        val distrib_deps = dependencies.collect { case (d, None) => d }.distinct
        val afp_deps = dependencies.collect { case (_, Some(d)) if d != e => d }.distinct
        as_json(e, distrib_deps, afp_deps)
    }

    println("[" + commas(result) + "]")
  }

}
