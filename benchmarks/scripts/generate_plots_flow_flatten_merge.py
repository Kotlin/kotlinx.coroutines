import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

input_file = "jmh-result.csv"
output_file = "flow-flatten-merge.svg"
elements = 100000
benchmark_name = "benchmarks.flow.FlowFlattenMergeBenchmark.flattenMerge"
csv_columns = ["Benchmark", "Score", "Score Error (99.9%)", "Unit", "Param: concurrency", "Param: flows"]
rename_columns = {"Benchmark": "benchmark", "Score" : "score", "Score Error (99.9%)" : "score_error", "Unit" : "unit",
                  "Param: concurrency" : "concurrency", "Param: flows" : "flows"}

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']

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
    plt.ylabel(data.unit.unique()[0])
    plt.xlabel('concurrency')
    plt.xticks(data.concurrency.unique())

    colour_gen = next_colour()
    marker_gen = next_marker()
    for flows in data.flows.unique():
        gen_colour = next(colour_gen)
        gen_marker = next(marker_gen)
        res = data[(data.flows == flows)]
        plt.plot(res.concurrency, res.score*elements, label="flows={}".format(flows), color=gen_colour, marker=gen_marker)
        plt.errorbar(x=res.concurrency, y=res.score*elements, yerr=res.score_error*elements, solid_capstyle='projecting', capsize=5)

data = pd.read_table(input_file, sep=",")
data = data[csv_columns].rename(columns=rename_columns)
data = data[(data.benchmark == benchmark_name)]
plt.figure(figsize=(20, 20))
draw(data, plt)
plt.legend(loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})
plt.tight_layout(pad=12, w_pad=2, h_pad=1)
plt.savefig(output_file, bbox_inches='tight')