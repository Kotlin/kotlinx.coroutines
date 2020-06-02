# Please, run this script from the root folder of this module.

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import locale
from matplotlib.ticker import FormatStrFormatter
from matplotlib.backends.backend_pdf import PdfPages

input_file = "build/reports/jmh/results.csv"
output_file = "out/channel-prod-cons.pdf"
mpmc_benchmark_name = "benchmarks.ChannelProducerConsumerBenchmark.mpmc"
spmc_benchmark_name = "benchmarks.ChannelProducerConsumerBenchmark.spmc"
csv_columns = ["Benchmark", "Score", "Score Error (99,9%)", "Unit", "Param: _0_dispatcher", "Param: _1_channel", "Param: _2_coroutines", "Param: _3_withSelect", "Param: _4_parallelism"]
rename_columns = {"Benchmark": "benchmark", "Score" : "score", "Score Error (99,9%)" : "score_error", "Unit" : "unit",
                  "Param: _0_dispatcher" : "dispatcher", "Param: _1_channel" : "channel", "Param: _2_coroutines" : "coroutines",
                  "Param: _3_withSelect" : "with_select", "Param: _4_parallelism" : "parallelism"}

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['#F7A3FF', '#EA00FF', '#2DA6C4', '#238199', '#1CD100', '#139100', '#fcae91', '#fb6a4a', '#8585D6', '#62629E', '#858585', '#2B2B2B', '#FFFF00', '#BABA00']

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

def draw(data, ax_arr):
    if isinstance(ax_arr, np.ndarray):
        flatten_ax_arr = ax_arr.flatten()
    else:
        flatten_ax_arr = [ax_arr]
    for ax in flatten_ax_arr:
        ax.set_xscale('log', basex=2)
        ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
        ax.grid(linewidth='0.5', color='lightgray')
        ax.set_ylabel(data.unit.unique()[0])
        ax.set_xlabel('parallelism')
        ax.set_xticks(data.parallelism.unique())

    i = 0
    for coroutines in data.coroutines.unique():
        for dispatcher in data.dispatcher.unique():
            flatten_ax_arr[i].set_title("coroutines={},dispatcher={}".format(int(coroutines), dispatcher))
            colour_gen = next_colour()
            marker_gen = next_marker()
            for channel in data.channel.unique():
                for with_select in data.with_select.unique():
                    gen_colour = next(colour_gen)
                    gen_marker = next(marker_gen)
                    res = data[(data.dispatcher == dispatcher) & (data.channel == channel) & (data.coroutines == coroutines) & (data.with_select == with_select)]
                    flatten_ax_arr[i].plot(res.parallelism, res.score, label="channel={},with_select={}".format(channel, with_select), color=gen_colour, marker=gen_marker, linewidth=2.2)
#                     flatten_ax_arr[i].errorbar(x=res.parallelism, y=res.score, yerr=res.score_error, solid_capstyle='projecting', label="channel={},coroutines={},with_select={}".format(channel, coroutines, with_select), capsize=4, color=gen_colour, marker=gen_marker)
            i += 1

def draw_cons_prod(data, suptitle, pdf):
    plt.rcParams.update({'font.size': 15})
    fig, ax_arr = plt.subplots(nrows=2, ncols=len(data.dispatcher.unique()), figsize=(20, 15))
    draw(data, ax_arr)
    if isinstance(ax_arr, np.ndarray): ax = ax_arr[0]
    else: ax = ax_arr
    lines, labels = ax.get_legend_handles_labels()
    fig.suptitle(suptitle, fontsize=15, y=1)
    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=2, frameon=False, borderaxespad=2, prop={'size': 15})

    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
    pdf.savefig(bbox_inches='tight')

def genFile(pdf):
    langlocale = locale.getdefaultlocale()[0]
    locale.setlocale(locale.LC_ALL, langlocale)
    dp = locale.localeconv()['decimal_point']
    data = pd.read_csv(input_file, sep=",", decimal=dp)
    data = data[csv_columns].rename(columns=rename_columns)
    mpmc_data = data[(data.benchmark == mpmc_benchmark_name)]
    draw_cons_prod(mpmc_data, "mpmc", pdf)
    spmc_data = data[(data.benchmark == spmc_benchmark_name)]
    draw_cons_prod(spmc_data, "spmc", pdf)

with PdfPages(output_file) as pdf:
    genFile(pdf)
