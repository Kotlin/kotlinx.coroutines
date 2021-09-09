# To run this script run the command 'python3 scripts/generate_plots_flow_flatten_merge.py' in the /benchmarks folder


import pandas as pd
import sys
import locale
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

input_file = "build/reports/jmh/results.csv"
output_file = "out/flow-flatten-merge.svg"
# Please change the value of this variable according to the FlowFlattenMergeBenchmarkKt.ELEMENTS
elements = 100000
benchmark_name = "benchmarks.flow.FlowFlattenMergeBenchmark.flattenMerge"
csv_columns = ["Benchmark", "Score", "Unit", "Param: concurrency", "Param: flowsNumberStrategy"]
rename_columns = {"Benchmark": "benchmark", "Score" : "score", "Unit" : "unit",
                  "Param: concurrency" : "concurrency", "Param: flowsNumberStrategy" : "flows"}

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua', 'black', 'silver']

def next_colour():
    i = 0
    while True:
        yield colours[i % len(colours)]
        i += 1

def next_marker():
    i = 0
    while True:
        yield markers[i % len(markers)]
        i += 1

def draw(data, plt):
    plt.xscale('log', basex=2)
    plt.gca().xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    plt.grid(linewidth='0.5', color='lightgray')
    if data.unit.unique()[0] != "ops/s":
        print("Unexpected time unit: " + data.unit.unique()[0])
        sys.exit(1)
    plt.ylabel("elements / ms")
    plt.xlabel('concurrency')
    plt.xticks(data.concurrency.unique())

    colour_gen = next_colour()
    marker_gen = next_marker()
    for flows in data.flows.unique():
        gen_colour = next(colour_gen)
        gen_marker = next(marker_gen)
        res = data[(data.flows == flows)]
#         plt.plot(res.concurrency, res.score*elements/1000, label="flows={}".format(flows), color=gen_colour, marker=gen_marker)
        plt.errorbar(x=res.concurrency, y=res.score*elements/1000, yerr=res.score_error*elements/1000, solid_capstyle='projecting',
                     label="flows={}".format(flows), capsize=4, color=gen_colour, linewidth=2.2)

langlocale = locale.getdefaultlocale()[0]
locale.setlocale(locale.LC_ALL, langlocale)
dp = locale.localeconv()['decimal_point']
if dp == ",":
    csv_columns.append("Score Error (99,9%)")
    rename_columns["Score Error (99,9%)"] = "score_error"
elif dp == ".":
    csv_columns.append("Score Error (99.9%)")
    rename_columns["Score Error (99.9%)"] = "score_error"
else:
    print("Unexpected locale delimeter: " + dp)
    sys.exit(1)
data = pd.read_csv(input_file, sep=",", decimal=dp)
data = data[csv_columns].rename(columns=rename_columns)
data = data[(data.benchmark == benchmark_name)]
plt.rcParams.update({'font.size': 15})
plt.figure(figsize=(12.5, 10))
draw(data, plt)
plt.legend(loc='upper center', borderpad=0, bbox_to_anchor=(0.5, 1.3), ncol=2, frameon=False, borderaxespad=2, prop={'size': 15})
plt.tight_layout(pad=12, w_pad=2, h_pad=1)
plt.savefig(output_file, bbox_inches='tight')
