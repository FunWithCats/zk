#!/bin/sh
sbt clean compile && sbt run | grep -Ev "^[^ a-zA-Z0-9]*\[" | tee output.xml && \
cat output.xml | xmllint --recover - | xmllint --format  - > output-clean.xml

[ "X$(uname)" = "XLinux" ] && [ -f "output-clean.xml" ] && xdg-open output-clean.xml


