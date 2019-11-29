#!/bin/bash
cd "$(dirname "$0")"

server="https://top-prover.top"

echo -n 'user: '
read user
echo -n 'password: '
read -s password
curl -v -c .cookie -F "user=${user}" -F "password=${password}" "${server}/login"
