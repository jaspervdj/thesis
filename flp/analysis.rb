#!/usr/bin/env ruby

require 'fileutils'
require 'open3'
require 'tempfile'

TMP = 'tmp'
ROOT = FileUtils.pwd

def valid_name(name)
  !name.include?('$')
end

def results(output)
  folds = {}
  folds_per_type = Hash.new { |h, k| h[k] = [] }

  output.lines.each do |line|
    words = line.split
    if words[0] == 'RewriteResult:' && words.last != 'NoFold' then
      name = words[1]
      if valid_name(name) && !folds[name]
        fold_type = words.last
        folds_per_type[fold_type] << name
        folds[name] = true
      end
    end
  end

  folds_per_type.each do |fold_type, names|
    puts "#{fold_type}: #{names.length}"
    puts "#{fold_type}: #{names.join(', ')}"
  end
end

def compile(command, name)
  print "Compiling #{name}: "

  start = Time.now
  output = `#{command}`
  status = $?

  elapsed = (Time.now - start).floor
  if status.success? then
    print "success (#{elapsed}s)\n"
    results(output)
  else
    print "exit code #{status.exitstatus} (#{elapsed}s)\n"
  end

  log = `mktemp /tmp/whatmorpism-XXXXX`.chomp
  File.open(log, 'w') { |f| f.write(output) }
  puts "Log written to #{log}"
end

def compile_zip(name)
  # Preventive cleanup
  FileUtils.rm_rf TMP

  # Move over zip file
  FileUtils.mkdir TMP
  FileUtils.cp name, TMP

  # Go to tmp dir and unzip
  FileUtils.cd TMP
  `unzip "#{name}"`

  # Analysis
  command = 'ghc --make -package what-morphism -fplugin=WhatMorphism Main.hs 2>&1'
  compile(command, name)

  # Remove tmp dir
  FileUtils.cd ROOT
  FileUtils.rm_r TMP
end

def compile_cabal(name)
  package = name.chomp('.tar.gz')
  `tar -xzf #{name}`

  FileUtils.cd package
  cabal_file = Dir.glob('*.cabal').first

  patched = File.read(cabal_file).gsub(/^(library)(\s+)/i) do
    "#{$1}#{$2}" +
      "build-depends: what-morphism#{$2}" +
      "ghc-options: -fplugin=WhatMorphism#{$2}"
  end

  File.open(cabal_file, 'w') { |f| f.write(patched) }

  command = 'cabal configure && cabal build 2>&1'
  compile(command, package)

  FileUtils.cd ROOT
  FileUtils.rm_r package
end

file = ARGV[0]

if file.end_with? '.zip'
  compile_zip(file)
elsif file.end_with? '.tar.gz'
  compile_cabal(file)
end
