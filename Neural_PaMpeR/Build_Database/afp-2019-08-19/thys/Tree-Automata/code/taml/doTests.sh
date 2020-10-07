#/!bin/sh

ML_FILE="$PWD/Main.ml"

# Configuration, adopt these to your Taml-installation
TAML_DIR="$HOME/opt/src/Timbuk_Distrib"

if test ! -d "$TAML_DIR" -a -f "$TAML_DIR/taml" -a -x "$TAML_DIR/taml"; then
  echo "Set the TAML_DIR variable to a valid Taml-installation. Current value: $TAML_DIR"
  exit 1
fi


pushd $TAML_DIR

echo "#use \"$ML_FILE\";;" | ./taml
res=$?
popd
exit $res
