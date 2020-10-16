#!/bin/sh

tar -czf Refine_Imperative_HOL.tgz --exclude="Refine_Imperative_HOL.tgz" --exclude-from=TGZ_EXCLUDE --exclude-tag-all=NOTGZ --exclude-backups --exclude-vcs --transform 's|^|Refine_Imperative_HOL/|' *
