import argparse
import pandas as pd
import matplotlib.pyplot as plt

# Parse command-line arguments
parser = argparse.ArgumentParser(description="Plot throughput benchmark chart")
parser.add_argument("--len5_report_file",
                    help="CSV report with IPC data coming from LEN5")
parser.add_argument("--xheep_report_file",
                    help="CSV report with IPC data coming from X-HEEP")
parser.add_argument("--chart_file",
                    help="Output PNG chart file")

args = parser.parse_args()

# Use LaTeX to render text
# plt.rc("text", usetex=True)
plt.rc("font", family="sans-serif")

# Initialization
len5_report_file = args.len5_report_file
chart_file = args.chart_file
xheep_report_file = args.xheep_report_file

# Read CSV report with data
df_len5 = pd.read_csv(len5_report_file, sep=",", header=0)
df_x_heep = pd.read_csv(xheep_report_file, sep=",", header=0)
new_headers = {'Instructions' : 'LEN5 Instructions', 'Cycles' : 'LEN5 Cycles', 'IPC' : 'LEN5 IPC'}
df_len5.rename(columns=new_headers, inplace=True)
new_headers = {'Instructions' : 'CV32E40P Instructions', 'Cycles' : 'CV32E40P Cycles', 'IPC' : 'CV32E40P IPC'}
df_x_heep.rename(columns=new_headers, inplace=True)

df = pd.merge(df_len5, df_x_heep, on='Benchmark')
df.sort_values(by='Benchmark', inplace=True)
df['IPC Improvement'] =  df['LEN5 IPC'] / df['CV32E40P IPC']
df['Latency Improvement'] =    df['CV32E40P Cycles'] / df['LEN5 Cycles']

colors = ["#6d1a3680", "#6d1a36c0", "#6d1a36ff", "#00748080", "#007480c0", "#007480ff"]
df_bars = df[["Benchmark", "LEN5 IPC", "CV32E40P IPC", "IPC Improvement", "Latency Improvement"]]

df_bars.plot(kind="bar", rot=0, x='Benchmark', title="Instructions per Clock Cycle comparison (higher is better)", ylabel="Instructions Per Cycle (IPC)", xlabel="Benchmark application", figsize=(12, 5), grid=False, width=0.8, color=colors)

# Draw horizontal grid only
plt.gca().yaxis.grid(True)

# Set suptitle
plt.suptitle("LEN5 Processor IPC Improvement", fontweight="bold", fontsize="x-large", color="#3d3d3dff")

# Superpose an horizontal line at y=1 with label "CPU"
plt.axhline(y=1, color="#3d3d3dff", linestyle="--")
# plt.text(-0.62, 2, "CPU", color="#3d3d3dff", rotation=0, fontsize="small")

# Set Y max value
# plt.gca().set_ylim([0, 1]) //TODO uncomment this if just IPC

# Add 'x' to the y-axis step labels
# plt.gca().yaxis.set_major_formatter(lambda x, pos: str(int(x)) + "x")

# Set legend titles
plt.gca().set_title(plt.gca().get_title(), fontsize="large", color="#3d3d3dff")
plt.gca().legend(title="Processor")
plt.gca().set_xlabel(plt.gca().get_xlabel(), fontweight="bold")
plt.gca().set_ylabel(plt.gca().get_ylabel(), fontweight="bold")

plt.savefig(chart_file, dpi=600, bbox_inches="tight")
