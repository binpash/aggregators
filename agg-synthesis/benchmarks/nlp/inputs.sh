#!/bin/bash

cd "$(realpath $(dirname "$0"))"
mkdir -p inputs
cd inputs

if [ ! -f ./book_links.txt ]; then
    # wget -O book_links.txt "https://atlas-group.cs.brown.edu/data/gutenberg/books.txt"
    curl "https://atlas-group.cs.brown.edu/data/gutenberg/books.txt" >book_links.txt
    if [ ! -f book_links.txt ]; then
        echo "Failed to download book_links.txt"
        exit 1
    fi
fi

if [ ! -f ./genesis ]; then
    curl -sf https://atlas-group.cs.brown.edu/data/gutenberg/8/0/0/8001/8001.txt >genesis
fi

if [ ! -f ./exodus ]; then
    curl -sf https://atlas-group.cs.brown.edu/data/gutenberg/3/3/4/2/33420/33420-0.txt >exodus
fi

if [ ! -e ./pg ]; then
    mkdir pg
    cd pg
    book_count=120

    head -n $book_count ../book_links.txt | while IFS= read -r line; do
        full_url="https://atlas-group.cs.brown.edu/data/gutenberg/${line}"
        echo "Downloading $full_url"
        # wget -q "$full_url"
        FILE=$(echo "$line" | awk -F/ '{print $NF}') # get last item in path
        curl https://atlas-group.cs.brown.edu/data/gutenberg/${line} >"$FILE"
    done

    cd ..
fi

if [ ! -e ./pg-small ]; then
    mkdir pg-small
    cd pg-small
    book_count=10

    # get top 10 of book_links.txt links
    head -n $book_count ../book_links.txt | while IFS= read -r line; do
        echo "$line"
        full_url="https://atlas-group.cs.brown.edu/data/gutenberg/${line}"
        echo "Downloading $full_url"
        # wget -q "$full_url"
        FILE=$(echo "$line" | awk -F/ '{print $NF}') # get last item in path
        curl https://atlas-group.cs.brown.edu/data/gutenberg/${line} >"$FILE"
    done

    cd ..
fi
