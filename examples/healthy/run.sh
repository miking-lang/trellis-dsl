case $1 in
  run)
    trellis --output-dir . healthy.trellis > /dev/null
    python3 runner.py
    ;;
  clean)
    rm -rf *generated* viterbi.py __init__.py __pycache__
    ;;
  *)
    >&2 echo "Expected argument 'run' or 'clean'"
    exit 1
    ;;
esac
