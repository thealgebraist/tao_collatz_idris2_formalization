#!/usr/bin/env bash
#
# Generate the "handwritten" margin/inline notes for central-theorem.tex.
#
# Each note is authored as an SVG that sets its text in a handwriting-imitation
# font (DkgHandwriting, from the fonts-dkg-handwriting package) and is then
# rendered to a self-contained PDF with rsvg-convert.  The PDFs are what the
# LaTeX document \includegraphics-es into the margins and body.
#
# Requires: rsvg-convert (librsvg2-bin) and a handwriting font.
#
set -euo pipefail
cd "$(dirname "$0")/handwritten"

INK="#12307a"      # blue "pen"
RED="#a01818"      # red "pen"
GRN="#1c6b2a"      # green "pencil"

emit () {  # emit <name> <svg-body-file-content-on-stdin>
  local name="$1"
  cat > "${name}.svg"
  rsvg-convert -f pdf -o "${name}.pdf" "${name}.svg"
  echo "  built ${name}.pdf"
}

# 1. slogan: Syracuse is the odd part of Collatz
emit hw_syracuse <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="120" viewBox="0 0 320 120">
  <text x="8" y="34" font-family="DkgHandwriting" font-size="27" fill="${INK}"
        transform="rotate(-2.5 8 34)">Syracuse = the</text>
  <text x="8" y="66" font-family="DkgHandwriting" font-size="27" fill="${INK}"
        transform="rotate(-2.5 8 66)">odd part of the</text>
  <text x="8" y="98" font-family="DkgHandwriting" font-size="27" fill="${INK}"
        transform="rotate(-2.5 8 98)">Collatz map!</text>
  <path d="M6 108 C 90 100, 200 116, 300 104" stroke="${RED}" stroke-width="2.4"
        fill="none" stroke-linecap="round"/>
</svg>
EOF

# 2. the deep analytic part
emit hw_deep <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="120" viewBox="0 0 320 120">
  <text x="8" y="32" font-family="DkgHandwriting" font-size="26" fill="${RED}"
        transform="rotate(3 8 32)">the deep part</text>
  <text x="8" y="62" font-family="DkgHandwriting" font-size="26" fill="${RED}"
        transform="rotate(3 8 62)">lives here!</text>
  <text x="8" y="94" font-family="DkgHandwriting" font-size="22" fill="${INK}"
        transform="rotate(3 8 94)">(Prop 1.9 &amp; 7.8)</text>
</svg>
EOF

# 3. numeric sanity check
emit hw_check <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="120" viewBox="0 0 320 120">
  <text x="8" y="30" font-family="DkgHandwriting" font-size="24" fill="${GRN}"
        transform="rotate(-2 8 30)">sanity check:</text>
  <text x="14" y="60" font-family="DkgHandwriting" font-size="24" fill="${INK}"
        transform="rotate(-2 14 60)">Col(3) = 10</text>
  <text x="14" y="90" font-family="DkgHandwriting" font-size="24" fill="${INK}"
        transform="rotate(-2 14 90)">Syr(7) = 11</text>
</svg>
EOF

# 4. no believe_me
emit hw_nobelieveme <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="90" viewBox="0 0 320 90">
  <text x="8" y="34" font-family="DkgHandwriting" font-size="26" fill="${GRN}"
        transform="rotate(-3 8 34)">all machine-checked</text>
  <text x="8" y="66" font-family="DkgHandwriting" font-size="26" fill="${GRN}"
        transform="rotate(-3 8 66)">no believe_me :)</text>
</svg>
EOF

# 5. four arrows glued
emit hw_fourarrows <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="110" viewBox="0 0 320 110">
  <text x="8" y="32" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(2 8 32)">the whole proof =</text>
  <text x="8" y="62" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(2 8 62)">just 4 arrows</text>
  <text x="8" y="92" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(2 8 92)">glued together</text>
  <path d="M175 84 C 210 88, 250 80, 300 86" stroke="${RED}" stroke-width="2.2" fill="none"/>
  <path d="M290 80 L 302 86 L 289 92" stroke="${RED}" stroke-width="2.2" fill="none"
        stroke-linecap="round" stroke-linejoin="round"/>
</svg>
EOF

# 6. almost all
emit hw_almostall <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="120" viewBox="0 0 320 120">
  <text x="8" y="32" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(-2 8 32)">"almost all" =</text>
  <text x="8" y="62" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(-2 8 62)">tiny exceptional</text>
  <text x="8" y="92" font-family="DkgHandwriting" font-size="25" fill="${INK}"
        transform="rotate(-2 8 92)">set (log-small)</text>
</svg>
EOF

# 7. threshold grows
emit hw_threshold <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="120" viewBox="0 0 320 120">
  <text x="8" y="32" font-family="DkgHandwriting" font-size="24" fill="${RED}"
        transform="rotate(2.5 8 32)">need a threshold</text>
  <text x="8" y="62" font-family="DkgHandwriting" font-size="24" fill="${RED}"
        transform="rotate(2.5 8 62)">that still grows</text>
  <text x="8" y="92" font-family="DkgHandwriting" font-size="24" fill="${INK}"
        transform="rotate(2.5 8 92)">on odd fibres</text>
</svg>
EOF

# 8. title doodle
emit hw_title <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="820" height="120" viewBox="0 0 820 120">
  <text x="10" y="60" font-family="DkgHandwriting" font-size="52" fill="${INK}"
        transform="rotate(-2 10 60)">3n + 1 ... almost bounded!</text>
  <path d="M12 80 C 220 72, 560 90, 800 76" stroke="${RED}" stroke-width="3" fill="none"
        stroke-linecap="round"/>
  <path d="M12 90 C 240 84, 550 100, 800 88" stroke="${RED}" stroke-width="1.6" fill="none"
        stroke-linecap="round"/>
</svg>
EOF

# 9. QED flourish
emit hw_qed <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="260" height="90" viewBox="0 0 260 90">
  <text x="8" y="46" font-family="DkgHandwriting" font-size="34" fill="${GRN}"
        transform="rotate(-4 8 46)">and that's it!</text>
  <path d="M8 60 C 70 54, 150 70, 235 56" stroke="${GRN}" stroke-width="2.4" fill="none"
        stroke-linecap="round"/>
</svg>
EOF

# 10. odd threshold is an assumption
emit hw_assume <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="320" height="90" viewBox="0 0 320 90">
  <text x="8" y="34" font-family="DkgHandwriting" font-size="25" fill="${RED}"
        transform="rotate(-2 8 34)">taken as an honest</text>
  <text x="8" y="66" font-family="DkgHandwriting" font-size="25" fill="${RED}"
        transform="rotate(-2 8 66)">hypothesis, not faked</text>
</svg>
EOF

echo "All handwritten notes generated."
