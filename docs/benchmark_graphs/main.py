import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime, timedelta

# uv run python main.py

N_DAYS_SHOWN = 60

def create_duration_graph(data, target, target_label, title, y_legend, file):
    dates = []
    values = []

    for day, duration in data:
        dates.append(datetime.strptime(day, '%Y-%m-%d'))
        values.append(duration)

    color = '#2E86AB'

    _, ax = plt.subplots(figsize=(10, 6))
    ax.plot(dates, values, marker='o', linewidth=2,
            markersize=7, color=color)

    min_date = min(dates)
    max_date = max(dates)
    date_range = max_date - min_date
    if date_range < timedelta(days=N_DAYS_SHOWN):
        max_date = min_date + timedelta(days=N_DAYS_SHOWN)
    ax.set_xlim(min_date - timedelta(days=1), max_date + timedelta(days=1))

    ax.xaxis.set_major_locator(mdates.WeekdayLocator(interval=1))
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))

    plt.setp(ax.xaxis.get_majorticklabels(), rotation=50, ha='right')

    ax.axhline(y=target, color=color, linestyle='--',
               linewidth=2, label=target_label)

    ax.set_ylabel(y_legend, fontsize=12)
    ax.set_title(title, fontsize=16, pad=15)
    ax.grid(True, alpha=0.3)
    ax.legend()

    ax.set_ylim(0, max(max(values), target) * 1.1)

    plt.tight_layout()
    plt.savefig(f'graphs/{file}.svg', format='svg', bbox_inches='tight')


if __name__ == "__main__":

    create_duration_graph(data=[
        ('2025-08-27', 85000),
        ('2025-08-30', 95000),
        ('2025-09-09', 108000),
        ('2025-09-14', 108000),
        ('2025-09-28', 125000),
        ('2025-10-01', 185000),
        ('2025-10-12', 195000),
        ('2025-10-13', 205000),
        ('2025-10-18', 210000),
    ], target=300_000, target_label="Target (300.000 Poseidon2 / s)", title="Raw Poseidon2", y_legend="Poseidons proven / s", file="raw_poseidons")

    create_duration_graph(data=[
        ('2025-08-27', 2.7),
        ('2025-09-07', 1.4),
        ('2025-09-09', 1.32),
        ('2025-09-10', 0.970),
        ('2025-09-14', 0.825),
        ('2025-09-28', 0.725),
        ('2025-10-01', 0.685),
        ('2025-10-03', 0.647),
        ('2025-10-12', 0.569),
        ('2025-10-13', 0.521),
        ('2025-10-18', 0.411),
    ], target=0.125, target_label="Target (0.125 s)", title="Recursive WHIR opening", y_legend="Proving time (s)", file="recursive_whir_opening")

    create_duration_graph(data=[
        ('2025-08-27', 14.2),
        ('2025-09-02', 13.5),
        ('2025-09-03', 9.4),
        ('2025-09-09', 8.02),
        ('2025-09-10', 6.53),
        ('2025-09-14', 4.65),
        ('2025-09-28', 3.63),
        ('2025-10-01', 2.9),
        ('2025-10-03', 2.81),
        ('2025-10-07', 2.59),
        ('2025-10-12', 2.33),
        ('2025-10-13', 2.13),
        ('2025-10-18', 1.96),
    ], target=0.5, target_label="Target (0.5 s)", title="500 XMSS aggregated: proving time", y_legend="Proving time (s)", file="xmss_aggregated_time")

    create_duration_graph(data=[
        ('2025-08-27', 14.2 / 0.92),
        ('2025-09-02', 13.5 / 0.82),
        ('2025-09-03', 9.4 / 0.82),
        ('2025-09-09', 8.02 / 0.72),
        ('2025-09-10', 6.53 / 0.72),
        ('2025-09-14', 4.65 / 0.72),
        ('2025-09-28', 3.63 / 0.63),
        ('2025-10-01', 2.9 / 0.42),
        ('2025-10-03', 2.81 / 0.42),
        ('2025-10-07', 2.59 / 0.42),
        ('2025-10-12', 2.33 / 0.40),
        ('2025-10-13', 2.13 / 0.38),
        ('2025-10-18', 1.96 / 0.37),
    ], target=2.0, target_label="Target (2x)", title="500 XMSS aggregated: zkVM overhead vs raw Poseidons", y_legend="", file="xmss_aggregated_overhead")
