import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

inputFile = "jmh-result.csv"
outputFile = "flatten-merge-plots.svg"
elements = 10000
benchmarkName="benchmarks.flow.FlattenMergeBenchmark.flattenMerge"

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
    data = data[(data.benchmark == benchmarkName)]

    plt.xscale('log', basex=2)
    plt.gca().xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    plt.grid(linewidth='0.5', color='lightgray')
    plt.ylabel(data.unit.unique()[0])
    plt.xlabel('parallelism')
    plt.xticks(data.concurrency.unique())

    colourGen = next_colour()
    markerGen = next_marker()
    for flows in data.flows.unique():
        genColour = next(colourGen)
        genMarker = next(markerGen)
        res = data[(data.flows == flows)]
        plt.plot(res.concurrency, res.score*elements, label="flows={}".format(flows), color=genColour, marker=genMarker)

def genFile():
    data = pd.read_table(inputFile, sep=",", skiprows=1, names=["benchmark","mode","threads","samples","score","scoreError","unit","concurrency","flows"])
    plt.figure(figsize=(20, 20))
    draw(data, plt)
    plt.legend(loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})
    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
    plt.savefig(outputFile, bbox_inches='tight')

genFile()