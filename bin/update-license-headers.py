#!/usr/bin/env python3
"""
Script to maintain license headers in .lean files.
Removes existing license headers and adds the new one from bin/license-header.txt.
Respects .gitignore patterns.
"""

import fnmatch
import os
import re
import sys
from pathlib import Path


def read_license_header(license_file_path):
    """Read the license header content from the specified file."""
    try:
        with open(license_file_path, 'r', encoding='utf-8') as f:
            content = f.read().strip()
        return content
    except FileNotFoundError:
        print(f"Error: License header file not found: {license_file_path}")
        sys.exit(1)


def format_license_header(license_content):
    """Format the license content with /- -/ comment syntax."""
    lines = license_content.split('\n')
    formatted_lines = ['/-'] + lines + ['-/']
    return '\n'.join(formatted_lines) + '\n\n'


def remove_existing_license_header(content):
    """Remove existing license header from the beginning of the file."""
    # Pattern to match license header block at the start of file
    # Matches from start of file, optional whitespace, /-, content, -/, optional whitespace
    pattern = r'^\s*/-.*?-/\s*\n*'

    # Use DOTALL flag to make . match newlines
    match = re.match(pattern, content, re.DOTALL)

    if match:
        # Remove the matched license header
        return content[match.end():]

    return content


def process_lean_file(file_path, new_license_header):
    """Process a single .lean file to update its license header."""
    try:
        # Read the current file content
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Remove existing license header
        content_without_header = remove_existing_license_header(content)

        # Add new license header
        new_content = new_license_header + content_without_header

        # Write back to file
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)

        print(f"Updated: {file_path}")
        return True

    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False


def read_gitignore_patterns(gitignore_path):
    """Read and parse .gitignore patterns."""
    patterns = []
    if os.path.exists(gitignore_path):
        with open(gitignore_path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    patterns.append(line)
    return patterns


def is_ignored(file_path, root_dir, gitignore_patterns):
    """Check if a file should be ignored based on .gitignore patterns."""
    # Get relative path from project root
    try:
        rel_path = os.path.relpath(file_path, root_dir)
    except ValueError:
        return False

    # Normalize path separators for cross-platform compatibility
    rel_path = rel_path.replace(os.sep, '/')

    # Check each gitignore pattern
    for pattern in gitignore_patterns:
        # Remove leading slash if present (anchored to root)
        if pattern.startswith('/'):
            pattern = pattern[1:]

        # Handle directory patterns (ending with /)
        if pattern.endswith('/'):
            dir_pattern = pattern[:-1]
            # Check if the path starts with the directory pattern
            if rel_path.startswith(dir_pattern + '/') or rel_path == dir_pattern:
                return True
            # For patterns like **/__pycache__/, check any directory level
            if pattern.startswith('**/'):
                dir_pattern = pattern[3:-1]  # Remove **/ and /
                path_parts = rel_path.split('/')
                for part in path_parts[:-1]:  # Exclude the filename
                    if fnmatch.fnmatch(part, dir_pattern):
                        return True
        else:
            # Handle file patterns
            if fnmatch.fnmatch(rel_path, pattern) or fnmatch.fnmatch(os.path.basename(rel_path), pattern):
                return True

    return False


def find_lean_files(root_dir):
    """Find all .lean files in the directory tree, respecting .gitignore."""
    gitignore_path = os.path.join(root_dir, '.gitignore')
    gitignore_patterns = read_gitignore_patterns(gitignore_path)

    lean_files = []
    for root, dirs, files in os.walk(root_dir):
        # Filter out ignored directories early to avoid walking into them
        dirs_to_remove = []
        for d in dirs:
            # Always ignore .lake directories regardless of location
            if d == '.lake':
                dirs_to_remove.append(d)
                continue
                
            dir_path = os.path.join(root, d)
            if is_ignored(dir_path, root_dir, gitignore_patterns):
                dirs_to_remove.append(d)

        for d in dirs_to_remove:
            dirs.remove(d)

        # Check files in current directory
        for file in files:
            if file.endswith('.lean'):
                file_path = os.path.join(root, file)
                if not is_ignored(file_path, root_dir, gitignore_patterns):
                    lean_files.append(file_path)

    return lean_files


def main():
    # Get the script directory and project root
    script_dir = Path(__file__).parent
    project_root = script_dir.parent

    # Path to the license header file
    license_header_file = script_dir / 'license-header.txt'

    print(f"Project root: {project_root}")
    print(f"License header file: {license_header_file}")

    # Read the license header content
    license_content = read_license_header(license_header_file)
    formatted_header = format_license_header(license_content)

    print("License header to be applied:")
    print("-" * 40)
    print(formatted_header)
    print("-" * 40)

    # Find all .lean files
    lean_files = find_lean_files(project_root)

    if not lean_files:
        print("No .lean files found.")
        return

    print(f"Found {len(lean_files)} .lean files:")
    for file in lean_files:
        print(f"  {file}")

    # Ask for confirmation
    response = input(f"\nProceed to update license headers in {len(lean_files)} files? (y/N): ")
    if response.lower() not in ['y', 'yes']:
        print("Operation cancelled.")
        return

    # Process each file
    success_count = 0
    for file_path in lean_files:
        if process_lean_file(file_path, formatted_header):
            success_count += 1

    print(f"\nCompleted: {success_count}/{len(lean_files)} files updated successfully.")


if __name__ == '__main__':
    main()
