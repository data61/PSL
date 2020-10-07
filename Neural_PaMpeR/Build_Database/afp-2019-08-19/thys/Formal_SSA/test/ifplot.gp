set style data linespoints
g(x) = c*x**d*log(x)**e
c=1e-7;d=1;e=2
fit g(x) "ifplot.data" using 1:2 via c, d, e
plot "ifplot.data" title "t", g(x) title sprintf("%.2g * n^{%.2g} * lg(n)^{%.2g}", c, d, e)
