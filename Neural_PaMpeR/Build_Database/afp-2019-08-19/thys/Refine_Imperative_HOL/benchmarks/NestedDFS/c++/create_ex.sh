#!/bin/bash
mkdir -p "../ex"

# Philosophers
echo "Philosophers (Size 6 may take several minutes on 2012 laptop hardware)"
name=phils
phi[0]="[] (one0 -> ((one0 U eat0) || []one0))"
phi[1]="[] (one0 -> !eat0)"

for ((i=1;i<=6;++i)); do 
  for ((j=0;j<=1;++j)); do
    echo "Size $i, phi_$j"
    file="../ex/$name.$i.$j.states"
    test -f $file || ./ess.pl $name.$i.pm "${phi[$j]}" > $file 2>/dev/null || echo "Error!"
  done  
done

# Peterson
echo "Peterson"
name=peterson
phi[0]="[](wait0 -> (<>cs0 || []!ncs0))"
phi[1]="[] (wait0 -> !cs0)"


for ((i=1;i<=4;++i)); do 
  for ((j=0;j<=1;++j)); do
    echo "Size $i, phi_$j"
    file="../ex/$name.$i.$j.states"
    
    test -f $file || ./ess.pl $name.$i.pm "${phi[$j]}" > $file 2>/dev/null || echo "Error!"
  done
done

