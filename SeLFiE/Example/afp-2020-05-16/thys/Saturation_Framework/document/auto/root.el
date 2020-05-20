(TeX-add-style-hook
 "root"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1") ("stmaryrd" "only" "bigsqcap") ("babel" "english")))
   (TeX-run-style-hooks
    "latex2e"
    "session"
    "fixltx2e"
    "article"
    "art11"
    "isabelle"
    "isabellesym"
    "fullpage"
    "graphicx"
    "comment"
    "mdframed"
    "inputenc"
    "fontenc"
    "lmodern"
    "subcaption"
    "amsmath"
    "amssymb"
    "amsthm"
    "nicefrac"
    "tikz"
    "stmaryrd"
    "wasysym"
    "babel"
    "pdfsetup"))
 :latex)

