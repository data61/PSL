(TeX-add-style-hook
 "root"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("color" "usenames" "dvipsnames") ("babel" "english")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "url")
   (TeX-run-style-hooks
    "latex2e"
    "session"
    "article"
    "art11"
    "isabelle"
    "isabellesym"
    "fullpage"
    "color"
    "document"
    "amssymb"
    "babel"
    "stmaryrd"
    "eufrak"
    "pdfsetup"
    "graphicx"
    "url")
   (LaTeX-add-bibliographies))
 :latex)

