"""Compatibility entry point: refresh locations without overwriting reviews.

The original script recreated the old supplemental inventory and reset review
fields. Correspondence now lives in docs/supplemental_results.json; edit that
file explicitly, then render it with this command or refresh_metadata.py.
"""
from refresh_metadata import main

if __name__ == '__main__':
    main()
