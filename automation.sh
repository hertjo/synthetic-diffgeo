#!/bin/bash

# ========== CONFIGURATION ==========
GIT_USER_NAME="hertjo"
GIT_USER_EMAIL="herter-johannes@web.de"
START_DATE="2024-08-01"
END_DATE="2024-10-02"
NUM_DAYS=50
TOTAL_COMMITS=78
BRANCH_NAME="main"
LOG_FILE="log.txt"
# ===================================

set -e  # Exit on error

# Set Git identity
git config user.name "$GIT_USER_NAME"
git config user.email "$GIT_USER_EMAIL"

# Detect macOS vs Linux date behavior
function date_to_epoch() {
  if date -d "$1" +%s >/dev/null 2>&1; then
    date -d "$1" +%s  # Linux
  else
    date -j -f "%Y-%m-%d" "$1" +%s  # macOS
  fi
}

function epoch_to_date() {
  if date -d "@$1" +%Y-%m-%d >/dev/null 2>&1; then
    date -d "@$1" +%Y-%m-%d  # Linux
  else
    date -r "$1" +%Y-%m-%d   # macOS
  fi
}

# Progress bar
function print_progress() {
  local current=$1
  local total=$2
  local width=40
  local filled=$((current * width / total))
  local bar=$(printf "%${filled}s" | tr ' ' '#')
  local pad=$(printf "%$((width - filled))s")
  printf "\rProgress: [${bar}${pad}] %d/%d commits" "$current" "$total"
}

# Convert start and end to epoch
START_EPOCH=$(date_to_epoch "$START_DATE")
END_EPOCH=$(date_to_epoch "$END_DATE")
RANGE_SECONDS=$((END_EPOCH - START_EPOCH))

# Generate full list of days in range
all_days=()
for ((offset = 0; offset <= RANGE_SECONDS; offset+=86400)); do
  all_days+=("$(epoch_to_date $((START_EPOCH + offset)))")
done

# Validate NUM_DAYS
if [ "$NUM_DAYS" -gt "${#all_days[@]}" ]; then
  echo "Error: NUM_DAYS ($NUM_DAYS) is greater than range of available days (${#all_days[@]})"
  exit 1
fi

# Shuffle and select NUM_DAYS
selected_days=($(printf "%s\n" "${all_days[@]}" | shuf -n "$NUM_DAYS"))

# Sort days chronologically
IFS=$'\n' sorted_days=($(sort <<<"${selected_days[*]}"))
unset IFS

# Initialize commit loop
commit_num=0
commits_left=$TOTAL_COMMITS
touch "$LOG_FILE"

for day in "${sorted_days[@]}"; do
  echo "Selected commit day: $day"

  # Random number of commits for this day (1–min(5, commits_left))
  max_today=$((commits_left < 5 ? commits_left : 5))
  commits_today=$((1 + RANDOM % max_today))

  for ((i=1; i<=commits_today; i++)); do
    echo "Work log: $day part $i" >> "$LOG_FILE"
    git add "$LOG_FILE"
    time_str="$day 12:$((RANDOM % 60)):00"

    GIT_COMMITTER_DATE="$time_str" \
    git commit --date="$time_str" -m "Work log: $day part $i" > /dev/null


    ((commit_num++))
    ((commits_left--))
    print_progress "$commit_num" "$TOTAL_COMMITS"

    if [ "$commits_left" -le 0 ]; then
      break 2
    fi
  done
done

echo -e "\n✅ Done! $commit_num commits made across $NUM_DAYS days."
