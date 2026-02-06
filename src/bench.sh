#!/bin/bash

echo -e "\033[32m=== XMSS: 1350 sigs, log-inv-rate=1 ===\033[0m"
cargo run --release -- xmss --n-signatures 1350 --log-inv-rate 1
sleep 1s

echo -e "\033[32m=== XMSS: 1350 sigs, log-inv-rate=2 ===\033[0m"
cargo run --release -- xmss --n-signatures 1350 --log-inv-rate 2
sleep 1s

echo -e "\033[32m=== XMSS: 1350 sigs, log-inv-rate=1, prox-gaps-conjecture ===\033[0m"
cargo run --release -- xmss --n-signatures 1350 --log-inv-rate 1 --prox-gaps-conjecture
sleep 1s

echo -e "\033[32m=== XMSS: 1350 sigs, log-inv-rate=2, prox-gaps-conjecture ===\033[0m"
cargo run --release -- xmss --n-signatures 1350 --log-inv-rate 2 --prox-gaps-conjecture
sleep 1s

echo -e "\033[32m=== Recursion: n=2 ===\033[0m"
cargo run --release -- recursion --n 2
sleep 1s

echo -e "\033[32m=== Recursion: n=2, prox-gaps-conjecture ===\033[0m"
cargo run --release -- recursion --n 2 --prox-gaps-conjecture
sleep 1s

echo -e "\033[32m=== Done ===\033[0m"
