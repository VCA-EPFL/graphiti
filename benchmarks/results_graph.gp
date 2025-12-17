set datafile separator ','

myOffset = 1
myWidth = 0.35
myWidth2 = 0.25
myWidth3 = 0.17
set style fill solid 1.0

#set boxwidth 0.5 relative
#set grid xtics

set linetype 2 lc rgb "#66c2a5"
set linetype 3 lc rgb "#fc8d62"
set linetype 4 lc rgb "#8da0cb"
set linetype 5 lc rgb "#e78ac3"
set linetype 6 lc rgb "#a6d854"

set size 1,1
set origin 0,0

#set key right top
set key outside
set key above

set logscale y
set format y "%.0f"

unset bmargin; unset lmargin; unset tmargin; unset rmargin
set multiplot layout 2,2

unset xtics

set arrow 1 front from graph 0, first myOffset to graph 1, first myOffset nohead ls -1 lc rgb "#e78ac3"
set yrange [0.1:7]

set format y "%.1f"
set ytics (0.1, 0.233894283743, 0.547065359676, 1.27955460463, 2.99280507758, 7)

set ylabel "(b) Rel. cycle count"

set size 0.5,0.4
set origin 0,0.6

plot sample [x=0:16:1] '+' us (x/2-0.5):(26/(int(x)%4!=1)) with filledcurves x1 fc rgb "#EEEEEE" notitle, \
     'raw_results.csv' every ::1 using 0:($3/$2):($0-myWidth2/2.):($0+myWidth2/2.):(myOffset):($3/$2):xtic(1) with boxxyerror notitle fs pattern 1, \
     '' every ::1 using 0:($4/$2):($0+(myWidth2)-myWidth2/2.):($0+(myWidth2)+myWidth2/2.):(myOffset):($4/$2):xtic(1) with boxxyerror notitle fs pattern 2, \
     '' every ::1 using 0:($5/$2):($0-(myWidth2)-myWidth2/2.):($0-(myWidth2)+myWidth2/2.):(myOffset):($5/$2):xtic(1) with boxxyerror notitle

unset yrange
set yrange [0:12]
set nologscale y

set format y "%.1f"
set ytics (0, 2, 4, 6, 8, 10, 12)

set ylabel "(c) Clock Period (ns)"

set size 0.5,0.4
set origin 0.5,0.6

unset arrow
# set arrow 1 front from graph 0, first 10 to graph 1, first 10 nohead ls -1 linecolor "#e41a1c" dashtype 2

plot sample [x=0:16:1] '+' us (x/2-0.5):(26/(int(x)%4!=1)) with filledcurves x1 fc rgb "#EEEEEE" notitle, \
     'raw_results.csv' every ::1 using 0:($7):($0+0.5*(myWidth3)-myWidth3/2.):($0+0.5*(myWidth3)+myWidth3/2.):(0):($7):xtic(1) with boxxyerror title "DF-OoO" fs pattern 1,\
     '' every ::1 using 0:($8):($0+1.5*(myWidth3)-myWidth3/2.):($0+1.5*(myWidth3)+myWidth3/2.):(0):($8):xtic(1) with boxxyerror title "Graphiti" fs pattern 2,\
'' every ::1 using 0:($9):($0-1.5*(myWidth3)-myWidth3/2.):($0-1.5*(myWidth3)+myWidth3/2.):(0):($9):xtic(1) with boxxyerror title "Vericert",\
     '' every ::1 using 0:($6):($0-0.5*(myWidth3)-myWidth3/2.):($0-0.5*(myWidth3)+myWidth3/2.):(0):($6):xtic(1) with boxxyerror title "DF-IO"

unset arrow
set arrow 1 front from graph 0, first myOffset to graph 1, first myOffset nohead ls -1 lc rgb "#e78ac3"

unset yrange
set ylabel "(a) Relative execution time"

set yrange [0.1:8]
set logscale y

set size 0.5,0.6
set origin 0,0

set format y "%.1f"
set ytics (0.1, 0.240224886796, 0.577079962364, 1.38628968631, 3.33021282962, 8)

set xtics scale 0 rotate by -90

plot sample [x=0:16:1] '+' us (x/2-0.5):(26/(int(x)%4!=1)) with filledcurves x1 fc rgb "#EEEEEE" notitle, \
     'raw_results.csv' every ::1 using 0:($11/$10):($0-myWidth2/2.):($0+myWidth2/2.):(myOffset):($11/$10):xtic(1) with boxxyerror notitle fs pattern 1, \
     '' every ::1 using 0:($12/$10):($0+(myWidth2)-myWidth2/2.):($0+(myWidth2)+myWidth2/2.):(myOffset):($12/$10):xtic(1) with boxxyerror notitle fs pattern 2, \
     '' every ::1 using 0:($13/$10):($0-(myWidth2)-myWidth2/2.):($0-(myWidth2)+myWidth2/2.):(myOffset):($13/$10):xtic(1) with boxxyerror notitle

unset yrange
set ylabel "(a) Rel. number of FFs"

set yrange [0.3:6]
set size 0.5,0.6
set origin 0.5,0

set format y "%.1f"
set ytics (0.3, 0.546169260909, 0.994336205202, 1.81025290096, 3.2956816299, 6)

set xtics scale 0 rotate by -90

plot sample [x=0:16:1] '+' us (x/2-0.5):(26/(int(x)%4!=1)) with filledcurves x1 fc rgb "#EEEEEE" notitle, \
     'raw_results.csv' every ::1 using 0:($20/$19):($0-myWidth2/2.):($0+myWidth2/2.):(myOffset):($20/$19):xtic(1) with boxxyerror notitle fs pattern 1,\
     '' every ::1 using 0:($21/$19):($0+(myWidth2)-myWidth2/2.):($0+(myWidth2)+myWidth2/2.):(myOffset):($21/$19):xtic(1) with boxxyerror notitle fs pattern 2, \
     '' every ::1 using 0:($22/$19):($0-(myWidth2)-myWidth2/2.):($0-(myWidth2)+myWidth2/2.):(myOffset):($22/$19):xtic(1) with boxxyerror notitle

unset multiplot
