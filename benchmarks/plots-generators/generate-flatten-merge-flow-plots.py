import pandas as pd
import random
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.colors import ListedColormap
from matplotlib.backends.backend_pdf import PdfPages

inputFile = "jmh-result.csv"
outputFile = "flatten-merge-plots.pdf"
elements = 10000
flattenMergeBenchmarkName="benchmarks.flow.FlattenMergeBenchmark.flattenMerge"

def nextColour():
    colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']

    for colour in colours:
        yield colour

def nextMarker():
    markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']

    for marker in markers:
        yield marker

def draw(data, ax):
    data = data[(data.benchmark == flattenMergeBenchmarkName)]

    ax.set_xscale('log', basex=2)
    ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    ax.grid(linewidth='0.5', color='lightgray')
    ax.set_ylabel(data.unit.unique()[0])
    ax.set_xlabel('parallelism')
    ax.set_xticks(data.concurrency.unique())

    colourGen = nextColour()
    markerGen = nextMarker()
    for flows in data.flows.unique():
        genColour = next(colourGen)
        genMarker = next(markerGen)
        res = data[(data.flows == flows)]
        ax.plot(res.concurrency, res.score*elements, label="flows={}".format(flows), color=genColour, marker=genMarker)

def genFile(pdf):
    data = pd.read_table(inputFile, sep=",", skiprows=1, names=["benchmark","mode","threads","samples","score","scoreError","unit","concurrency","flows"])
    fig, ax = plt.subplots(nrows=1, ncols=1, figsize=(20, 20))
    draw(data, ax)
    lines, labels = ax.get_legend_handles_labels()
    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})

    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
    pdf.savefig(bbox_inches='tight')

with PdfPages(outputFile) as pdf:
    genFile(pdf)