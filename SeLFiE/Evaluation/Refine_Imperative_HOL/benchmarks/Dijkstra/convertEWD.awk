#!/usr/bin/gawk -f


NF==3 {
  printf ("%d %d %d\n", $1, $2, ($3*100000000))
}

NF != 3 {print}
