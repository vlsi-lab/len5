import argparse
import pandas as pd
import matplotlib.pyplot as plt

# Parse command-line arguments
parser = argparse.ArgumentParser(description="Plot throughput benchmark chart")
parser.add_argument("report_file",
                    help="CSV report with throughput data")
parser.add_argument("chart_file",
                    help="Output PNG chart file")
args = parser.parse_args()

# Use LaTeX to render text
plt.rc("text", usetex=True)
plt.rc("font", family="sans-serif")

# Initialization
report_file = args.report_file
chart_file = args.chart_file

# Read CSV report with throughput data
# CSV format: Memory type,Kernel,Data type,CPU cycles,NM-Carus cycles,NM-Caesar cycles,NM-Carus gain,NM-Caesar gain,Kernel parameters
df = pd.read_csv(report_file, sep=",", header=0)

# Separate data by memory type
df_caesar = df.loc[df["Memory type"] == "caesar"]
df_carus = df.loc[df["Memory type"] == "carus"]

# Keep only relevant columns (reset index to zero)
df_cpu = df_carus[["Kernel", "Data type", "Output samples", "CPU cycles"]].reset_index(drop=True)
df_caesar = df_caesar[["Kernel", "Data type", "Output samples", "NM-Caesar cycles"]].reset_index(drop=True)
df_carus = df_carus[["Kernel", "Data type", "Output samples", "NM-Carus cycles"]].reset_index(drop=True)

# Rename columns
df_cpu = df_cpu.rename(columns={"CPU cycles": "Cycles"})
df_caesar = df_caesar.rename(columns={"NM-Caesar cycles": "Cycles"})
df_carus = df_carus.rename(columns={"NM-Carus cycles": "Cycles"})

# Compute the number of cycles per output sample
df_cpu["Cycles per output"] = df_cpu["Cycles"] / df_cpu["Output samples"]
df_caesar["Cycles per output"] = df_caesar["Cycles"] / df_caesar["Output samples"]
df_carus["Cycles per output"] = df_carus["Cycles"] / df_carus["Output samples"]

# Compute throughput gain in each data frame
df_cpu["CPU Gain"] = df_cpu["Cycles per output"] / df_cpu["Cycles per output"]
df_caesar["Caesar Gain"] = df_cpu["Cycles per output"] / df_caesar["Cycles per output"]
df_carus["Carus Gain"] = df_cpu["Cycles per output"] / df_carus["Cycles per output"]

# Keep only kernel, data type and throughput gain columns
df_cpu = df_cpu[["Kernel", "Data type", "CPU Gain"]]
df_caesar = df_caesar[["Kernel", "Data type", "Caesar Gain"]]
df_carus = df_carus[["Kernel", "Data type", "Carus Gain"]]

# Transform rows with the same data type into columns
df_cpu = df_cpu.pivot(index="Kernel", columns="Data type", values="CPU Gain")
df_caesar = df_caesar.pivot(index="Kernel", columns="Data type", values="Caesar Gain")
df_carus = df_carus.pivot(index="Kernel", columns="Data type", values="Carus Gain")

# Reorder columns
df_cpu = df_cpu[["int32", "int16", "int8"]]
df_caesar = df_caesar[["int32", "int16", "int8"]]
df_carus = df_carus[["int32", "int16", "int8"]]

# Reorder rows as [xor, add, mul, matmul, gemm, conv2d, relu, leaky-relu, maxpool]
df_cpu = df_cpu.reindex(["xor", "add", "mul", "matmul", "gemm", "conv2d", "relu", "leaky-relu", "maxpool"])
df_caesar = df_caesar.reindex(["xor", "add", "mul", "matmul", "gemm", "conv2d", "relu", "leaky-relu", "maxpool"])
df_carus = df_carus.reindex(["xor", "add", "mul", "matmul", "gemm", "conv2d", "relu", "leaky-relu", "maxpool"])

# Combine data frames, grouping columns by memory type
df = pd.concat([df_cpu, df_caesar, df_carus], axis=1, keys=["CPU", "NM-Caesar", "NM-Carus"])
print(df)

# Plot Caesar and Carus throughput bar chart
# - the kernel is the x-axis
# - the throughput gain is the y-axis
# - group columns by memory type
# - ignore the CPU
colors = ["#6d1a3680", "#6d1a36c0", "#6d1a36ff", "#00748080", "#007480c0", "#007480ff"]
df_bars = df[["NM-Caesar", "NM-Carus"]]
df_bars.plot(kind="bar", rot=0, title="Cycles per output sample: CPU + NMC vs. CPU only (higher is better)", ylabel="Throughput w.r.t. CPU", xlabel="Benchmark application", figsize=(12, 5), grid=False, width=0.8, color=colors)

# Draw horizontal grid only
plt.gca().yaxis.grid(True)

# Set suptitle
plt.suptitle("HEEPerator System Throughput Improvement", fontweight="bold", fontsize="x-large", color="#3d3d3dff")

# Superpose an horizontal line at y=1 with label "CPU"
plt.axhline(y=1, color="#3d3d3dff", linestyle="--")
plt.text(-0.62, 2, "CPU", color="#3d3d3dff", rotation=0, fontsize="small")

# Set Y max value
plt.gca().set_ylim([0, 100])

# Add 'x' to the y-axis step labels
plt.gca().yaxis.set_major_formatter(lambda x, pos: str(int(x)) + "x")

# Set legend titles
plt.gca().set_title(plt.gca().get_title(), fontsize="large", color="#3d3d3dff")
plt.gca().legend(title="(Memory type, SW data type)")
plt.gca().set_xlabel(plt.gca().get_xlabel(), fontweight="bold")
plt.gca().set_ylabel(plt.gca().get_ylabel(), fontweight="bold")

plt.savefig(chart_file, dpi=600, bbox_inches="tight")
