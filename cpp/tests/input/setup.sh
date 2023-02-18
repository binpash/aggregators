cd $(dirname $0)

[ "$1" = "-c" ] && rm-files 1M.txt words

eexit(){
  echo $1 'please email pash-devs@googlegroups.com'
  exit 1
}


append_nl_if_not(){
  ## Adds a newline at the end of a file if it doesn't already end in a newline.
  ## Used to prepare inputs for PaSh.
  if [ -z "$1" ]; then
    echo "No file argument given!"
    exit 1
  else
    if [ ! -f "$1" ]; then
      echo "File $1 doesn't exist!"
      exit 1
    else
      tail -c 1 "$1" | od -ta | grep -q nl
      if [ $? -eq 1 ]; then
        echo >> "$1"
      fi
    fi
  fi
}

if [ ! -f ./1M.txt ]; then
  curl -sf --connect-timeout 10 'ndr.md/data/dummy/1M.txt' > 1M.txt
  if [ $? -ne 0 ]; then
    curl -f 'http://www.gutenberg.org/files/2600/2600-0.txt' | head -c 1M > 1M.txt
    [ $? -ne 0 ] && eexit 'cannot find 1M.txt'
  fi
  append_nl_if_not ./1M.txt
fi

if [ ! -f ./words ]; then
  curl -sf --connect-timeout 10 'http://ndr.md/data/dummy/words' > words
  if [ $? -ne 0 ]; then
    curl -sf 'https://zenodo.org/record/7650885/files/words' > words
    if [ $? -ne 0 ]; then
      if [ $(uname) = 'Darwin' ]; then
        cp /usr/share/dict/web2 words || eexit "cannot find dict file"
      else
        # apt install wamerican-insane
        cp /usr/share/dict/words words || eexit "cannot find dict file"
      fi
    fi
  fi
  append_nl_if_not words
fi